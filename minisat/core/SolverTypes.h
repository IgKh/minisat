/***********************************************************************************[SolverTypes.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef Minisat_SolverTypes_h
#define Minisat_SolverTypes_h

#include <assert.h>

#include "minisat/mtl/IntTypes.h"
#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Vec.h"
#include "minisat/mtl/IntMap.h"
#include "minisat/mtl/Map.h"
#include "minisat/mtl/Alloc.h"

namespace Minisat {

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#if defined(MINISAT_CONSTANTS_AS_MACROS)
#define var_Undef (-1)
#else
  const Var var_Undef = -1;
#endif


struct Lit {
    int     x;

    // Use this as a constructor:
    friend Lit mkLit(Var var, bool sign = false);

    bool operator == (Lit p) const { return x == p.x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
};


inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
inline  bool sign      (Lit p)              { return p.x & 1; }
inline  int  var       (Lit p)              { return p.x >> 1; }

// Mapping Literals to and from compact integers suitable for array indexing:
inline  int  toInt     (Var v)              { return v; } 
inline  int  toInt     (Lit p)              { return p.x; } 
inline  Lit  toLit     (int i)              { Lit p; p.x = i; return p; } 

//const Lit lit_Undef = mkLit(var_Undef, false);  // }- Useful special constants.
//const Lit lit_Error = mkLit(var_Undef, true );  // }

const Lit lit_Undef = { -2 };  // }- Useful special constants.
const Lit lit_Error = { -1 };  // }

struct MkIndexLit { vec<Lit>::Size operator()(Lit l) const { return vec<Lit>::Size(l.x); } };

template<class T> class VMap : public IntMap<Var, T>{};
template<class T> class LMap : public IntMap<Lit, T, MkIndexLit>{};
class LSet : public IntSet<Lit, MkIndexLit>{};

//=================================================================================================
// Lifted booleans:
//
// NOTE: this implementation is optimized for the case when comparisons between values are mostly
//       between one variable and one constant. Some care had to be taken to make sure that gcc 
//       does enough constant propagation to produce sensible code, and this appears to be somewhat
//       fragile unfortunately.

class lbool {
    uint8_t value;

public:
    explicit lbool(uint8_t v) : value(v) { }

    lbool()       : value(0) { }
    explicit lbool(bool x) : value(!x) { }

    bool  operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
    bool  operator != (lbool b) const { return !(*this == b); }
    lbool operator ^  (bool  b) const { return lbool((uint8_t)(value^(uint8_t)b)); }

    lbool operator && (lbool b) const { 
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v); }

    lbool operator || (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};
inline int   toInt  (lbool l) { return l.value; }
inline lbool toLbool(int   v) { return lbool((uint8_t)v);  }

#if defined(MINISAT_CONSTANTS_AS_MACROS)
  #define l_True  (lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
  #define l_False (lbool((uint8_t)1))
  #define l_Undef (lbool((uint8_t)2))
#else
  const lbool l_True ((uint8_t)0);
  const lbool l_False((uint8_t)1);
  const lbool l_Undef((uint8_t)2);
#endif

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;
typedef RegionAllocator<uint32_t>::Ref CRef;

class Clause {
    struct {
    	unsigned type	   : 1;
    	unsigned mark      : 2;
        unsigned learnt    : 1;
        unsigned has_extra : 1;
        unsigned reloced   : 1;
        unsigned size      : 26; }                        header;
    union { Lit lit; float act; uint32_t abs; CRef rel; } data[0];

    friend class ClauseAllocator;

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(const vec<Lit>& ps, bool use_extra, bool learnt) {
        header.type		 = 0;
    	header.mark      = 0;
        header.learnt    = learnt;
        header.has_extra = use_extra;
        header.reloced   = 0;
        header.size      = ps.size();

        for (int i = 0; i < ps.size(); i++) 
            data[i].lit = ps[i];

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = 0;
            else
                calcAbstraction();
        }
    }

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    Clause(const Clause& from, bool use_extra){
        header           = from.header;
        header.has_extra = use_extra;   // NOTE: the copied clause may lose the extra field.

        for (int i = 0; i < from.size(); i++)
            data[i].lit = from[i];

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = from.data[header.size].act;
            else 
                data[header.size].abs = from.data[header.size].abs;
        }
    }

public:
    void calcAbstraction() {
        assert(header.has_extra);
        uint32_t abstraction = 0;
        for (int i = 0; i < size(); i++)
            abstraction |= 1 << (var(data[i].lit) & 31);
        data[header.size].abs = abstraction;  }


    int          size        ()      const   { return header.size; }
    void         shrink      (int i)         { assert(i <= size()); if (header.has_extra) data[header.size-i] = data[header.size]; header.size -= i; }
    void         pop         ()              { shrink(1); }
    bool         learnt      ()      const   { return header.learnt; }
    bool         has_extra   ()      const   { return header.has_extra; }
    uint32_t     mark        ()      const   { return header.mark; }
    void         mark        (uint32_t m)    { header.mark = m; }
    const Lit&   last        ()      const   { return data[header.size-1].lit; }

    bool         reloced     ()      const   { return header.reloced; }
    CRef         relocation  ()      const   { return data[0].rel; }
    void         relocate    (CRef c)        { header.reloced = 1; data[0].rel = c; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&         operator [] (int i)         { return data[i].lit; }
    Lit          operator [] (int i) const   { return data[i].lit; }
    operator const Lit* (void) const         { return (Lit*)data; }

    float&       activity    ()              { assert(header.has_extra); return data[header.size].act; }
    uint32_t     abstraction () const        { assert(header.has_extra); return data[header.size].abs; }

    Lit          subsumes    (const Clause& other) const;
    void         strengthen  (Lit p);
};

//=================================================================================================
// PbClause -- a simple class for representing a pseudo boolean constraint:
typedef int PbWeightType;
//typedef uint32_t PbPositiveWeightType;

enum PbConstraintSign {
	big_or_equal_sign 	= 0,
	big_sign			= 1,
	small_or_equal_sign = 2,
	small_sign 			= 3,
	equal_sign 			= 4
};

// A convenience structure for defining PB clauses in the general case
struct PbClauseDef {
	PbWeightType clause_const;
	PbConstraintSign clause_sign;
	vec<Lit> lits;
	vec<PbWeightType> coefs;

	// Default c'tor
	PbClauseDef(): clause_const(0), clause_sign(big_or_equal_sign) {
	}

	// Copy c'tor
	PbClauseDef(const PbClauseDef& other):
		clause_const(other.clause_const), clause_sign(other.clause_sign) {

		other.lits.copyTo(lits);
		other.coefs.copyTo(coefs);
	}
};

// A single entry within a PB clause (literal + coefficient)
struct PbLitPair {
	Lit lit;
	PbWeightType coef;

	PbLitPair(): lit(), coef() {}
	PbLitPair(const Lit& lit_, PbWeightType coef_): lit(lit_), coef(coef_) {
	}

	// Identity of the entry determined by its' literal
	bool operator ==(PbLitPair p) const { return lit == p.lit; }
	bool operator !=(PbLitPair p) const { return lit != p.lit; }
};

// An ordering for PbLitPairs, ranking them in decreasing coefficient size
struct PbLitPairWeightOrdering {
	bool operator ()(PbLitPair a, PbLitPair b) const { 
		if (a.coef > b.coef)
			return true;
		if (a.coef == b.coef)
			return toInt(a.lit) < toInt(b.lit);
		return false;
	}
};

// The actual constraint class
class PbClause {
	struct {
		unsigned type 	 : 1;
		unsigned reloced : 1;
		unsigned size	 : 30;
	} header;

	// The clause either has the core data (rhs and lhsSum), or it
	// is relocated and contains a pointer to the new location
	union {
		struct { PbWeightType rhs; PbWeightType lhsSum; } core;
		CRef rel;
	} auxData;

	PbLitPair data[0];

	friend class ClauseAllocator;

	// NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
	PbClause(const vec<PbLitPair>& lhs, PbWeightType rhs) {
		header.type	   = 1;
		header.reloced = 0;
		header.size    = lhs.size();

		auxData.core.lhsSum = 0;
		auxData.core.rhs = rhs;

		for (int i = 0; i < lhs.size(); i++) {
			data[i] = lhs[i];
			auxData.core.lhsSum += lhs[i].coef;
		}
	}

	// NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
	PbClause(const PbClause& from): header(from.header), auxData(from.auxData) {
		for (int i = 0; i < from.size(); i++)
			data[i] = from.data[i];
	}

public:
	int size() const {
		return header.size;
	}

	PbWeightType getRhs() const {
		return auxData.core.rhs;
	}

	PbWeightType getLhsSum() const {
		return auxData.core.lhsSum;
	}

	bool reloced   ()       const { return header.reloced; }
	CRef relocation()       const { return auxData.rel; }
	void relocate  (CRef c)       { header.reloced = 1; auxData.rel = c; }

	PbLitPair&       operator [] (int i)       { return data[i]; }
	const PbLitPair& operator [] (int i) const { return data[i]; }
};

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:

const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;
class ClauseAllocator
{
    RegionAllocator<uint32_t> ra;

    static uint32_t clauseWord32Size(int size, bool has_extra){
        return (sizeof(Clause) + (sizeof(Lit) * (size + (int)has_extra))) / sizeof(uint32_t); }

    static uint32_t pbClauseWord32Size(int size){
    	return (sizeof(PbClause) + (sizeof(PbLitPair) * size)) / sizeof(uint32_t); }

 public:
    enum { Unit_Size = RegionAllocator<uint32_t>::Unit_Size };

    bool extra_clause_field;

    ClauseAllocator(uint32_t start_cap) : ra(start_cap), extra_clause_field(false){}
    ClauseAllocator() : extra_clause_field(false){}

    void moveTo(ClauseAllocator& to){
        to.extra_clause_field = extra_clause_field;
        ra.moveTo(to.ra); }

    CRef alloc(const vec<Lit>& ps, bool learnt = false)
    {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        bool use_extra = learnt | extra_clause_field;
        CRef cid       = ra.alloc(clauseWord32Size(ps.size(), use_extra));
        new (lea(cid)) Clause(ps, use_extra, learnt);

        return cid;
    }

    CRef alloc(const Clause& from)
    {
        bool use_extra = from.learnt() | extra_clause_field;
        CRef cid       = ra.alloc(clauseWord32Size(from.size(), use_extra));
        new (lea(cid)) Clause(from, use_extra);
        return cid; }

    CRef allocPB(const vec<PbLitPair>& lhs, PbWeightType rhs)
    {
    	CRef cid = ra.alloc(pbClauseWord32Size(lhs.size()));
    	new (lea(cid)) PbClause(lhs, rhs);
    	return cid;
    }

    CRef allocPb(const PbClause& from)
    {
    	CRef cid = ra.alloc(pbClauseWord32Size(from.size()));
        new (lea(cid)) PbClause(from);
        return cid;
    }

    uint32_t size      () const      { return ra.size(); }
    uint32_t wasted    () const      { return ra.wasted(); }

    bool isPbClause(CRef r) const { return lea(r)->header.type > 0; }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](CRef r)         { return (Clause&)ra[r]; }
    const Clause& operator[](CRef r) const   { return (Clause&)ra[r]; }
    Clause*       lea       (CRef r)         { return (Clause*)ra.lea(r); }
    const Clause* lea       (CRef r) const   { return (Clause*)ra.lea(r); }
    CRef          ael       (const Clause* t){ return ra.ael((uint32_t*)t); }

    // Deref for PB clauses
    PbClause&       getPbClause(CRef r)       { return (PbClause&)ra[r]; }
    const PbClause& getPbClause(CRef r) const { return (PbClause&)ra[r]; }

    void free(CRef cid)
    {
    	if (isPbClause(cid)) {
    		PbClause& pbc = getPbClause(cid);
    		ra.free(pbClauseWord32Size(pbc.size()));
    	}
    	else {
    		Clause& c = operator[](cid);
    		ra.free(clauseWord32Size(c.size(), c.has_extra()));
    	}
    }

    void reloc(CRef& cr, ClauseAllocator& to)
    {
    	if (isPbClause(cr)) {
    		PbClause& pbc = getPbClause(cr);

    		if (pbc.reloced()) {
    			cr = pbc.relocation();
    		}
    		else {
    			cr = to.allocPb(pbc);
    			pbc.relocate(cr);
    		}
    	}
    	else {
    		Clause& c = operator[](cr);
        
    		if (c.reloced()) { cr = c.relocation(); return; }
        
    		cr = to.alloc(c);
    		c.relocate(cr);
    	}
    }
};

//=================================================================================================
// Simple iterator classes (for iterating over clauses and top-level assignments):

class ClauseIterator {
    const ClauseAllocator& ca;
    const CRef*            crefs;
public:
    ClauseIterator(const ClauseAllocator& _ca, const CRef* _crefs) : ca(_ca), crefs(_crefs){}

    void operator++(){ crefs++; }
    const Clause& operator*() const { return ca[*crefs]; }

    // NOTE: does not compare that references use the same clause-allocator:
    bool operator==(const ClauseIterator& ci) const { return crefs == ci.crefs; }
    bool operator!=(const ClauseIterator& ci) const { return crefs != ci.crefs; }
};


class TrailIterator {
    const Lit* lits;
public:
    TrailIterator(const Lit* _lits) : lits(_lits){}

    void operator++()   { lits++; }
    Lit  operator*() const { return *lits; }

    bool operator==(const TrailIterator& ti) const { return lits == ti.lits; }
    bool operator!=(const TrailIterator& ti) const { return lits != ti.lits; }
};


//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

template<class K, class Vec, class Deleted, class MkIndex = MkIndexDefault<K> >
class OccLists
{
    IntMap<K, Vec,  MkIndex> occs;
    IntMap<K, char, MkIndex> dirty;
    vec<K>                   dirties;
    Deleted                  deleted;

 public:
    OccLists(const Deleted& d, MkIndex _index = MkIndex()) :
        occs(_index), 
        dirty(_index), 
        deleted(d){}
    
    void  init      (const K& idx){ occs.reserve(idx); occs[idx].clear(); dirty.reserve(idx, 0); }
    Vec&  operator[](const K& idx){ return occs[idx]; }
    Vec&  lookup    (const K& idx){ if (dirty[idx]) clean(idx); return occs[idx]; }

    void  cleanAll  ();
    void  clean     (const K& idx);
    void  smudge    (const K& idx){
        if (dirty[idx] == 0){
            dirty[idx] = 1;
            dirties.push(idx);
        }
    }

    void  clear(bool free = true){
        occs   .clear(free);
        dirty  .clear(free);
        dirties.clear(free);
    }
};


template<class K, class Vec, class Deleted, class MkIndex>
void OccLists<K,Vec,Deleted,MkIndex>::cleanAll()
{
    for (int i = 0; i < dirties.size(); i++)
        // Dirties may contain duplicates so check here if a variable is already cleaned:
        if (dirty[dirties[i]])
            clean(dirties[i]);
    dirties.clear();
}


template<class K, class Vec, class Deleted, class MkIndex>
void OccLists<K,Vec,Deleted,MkIndex>::clean(const K& idx)
{
    Vec& vec = occs[idx];
    int  i, j;
    for (i = j = 0; i < vec.size(); i++)
        if (!deleted(vec[i]))
            vec[j++] = vec[i];
    vec.shrink(i - j);
    dirty[idx] = 0;
}


//=================================================================================================
// CMap -- a class for mapping clauses to values:


template<class T>
class CMap
{
    struct CRefHash {
        uint32_t operator()(CRef cr) const { return (uint32_t)cr; } };

    typedef Map<CRef, T, CRefHash> HashTable;
    HashTable map;
        
 public:
    typedef typename HashTable::Pair PairType;

    // Size-operations:
    void     clear       ()                           { map.clear(); }
    int      size        ()                const      { return map.elems(); }

    
    // Insert/Remove/Test mapping:
    void     insert      (CRef cr, const T& t){ map.insert(cr, t); }
    void     growTo      (CRef cr, const T& t){ map.insert(cr, t); } // NOTE: for compatibility
    void     remove      (CRef cr)            { map.remove(cr); }
    bool     has         (CRef cr, T& t)      { return map.peek(cr, t); }

    // Vector interface (the clause 'c' must already exist):
    const T& operator [] (CRef cr) const      { return map[cr]; }
    T&       operator [] (CRef cr)            { return map[cr]; }

    // Iteration (not transparent at all at the moment):
    int  bucket_count() const { return map.bucket_count(); }
    const vec<PairType>& bucket(int i) const { return map.bucket(i); }

    // Move contents to other map:
    void moveTo(CMap& other){ map.moveTo(other.map); }

    // TMP debug:
    void debug(){
        printf(" --- size = %d, bucket_count = %d\n", size(), map.bucket_count()); }
};


/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|  
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|  
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Lit Clause::subsumes(const Clause& other) const
{
    //if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
    //if (other.size() < size() || (!learnt() && !other.learnt() && (extra.abst & ~other.extra.abst) != 0))
    assert(!header.learnt);   assert(!other.header.learnt);
    assert(header.has_extra); assert(other.header.has_extra);
    if (other.header.size < header.size || (data[header.size].abs & ~other.data[other.header.size].abs) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* c   = (const Lit*)(*this);
    const Lit* d   = (const Lit*)other;

    for (unsigned i = 0; i < header.size; i++) {
        // search for c[i] or ~c[i]
        for (unsigned j = 0; j < other.header.size; j++)
            if (c[i] == d[j])
                goto ok;
            else if (ret == lit_Undef && c[i] == ~d[j]){
                ret = c[i];
                goto ok;
            }

        // did not find it
        return lit_Error;
    ok:;
    }

    return ret;
}

inline void Clause::strengthen(Lit p)
{
    remove(*this, p);
    calcAbstraction();
}

//=================================================================================================
}

#endif
