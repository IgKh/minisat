#ifndef Minisat_Debug_h
#define Minisat_Debug_h

#include <iostream>

#include "minisat/core/SolverTypes.h"

namespace Minisat {

inline std::ostream& operator<<(std::ostream& out, Lit l) {
	if (sign(l)) out << "~";
	out << var(l);
	return out;
}

inline std::ostream& operator<<(std::ostream& out, lbool b) {
	  if (b == l_True) out << "T";
	  if (b == l_False) out << "F";
	  if (b == l_Undef) out << "U";
	  return out;
}

inline std::ostream& operator<<(std::ostream& out, const PbClause& pbc) {
	for (int i = 0; i < pbc.size(); i++) {
		out << ((pbc[i].coef < 0) ? "-" : "+");
		out << pbc[i].coef << "x" << pbc[i].lit;
	}
	out << " >= " << pbc.getRhs();
	return out;
}

inline std::ostream& operator<<(std::ostream& out, const PbClauseDef& def) {
	for (int i = 0; i < def.lits.size(); i++) {
		if (def.coefs[i] < 0) {
			out << def.coefs[i];
		}
		else {
			out << "+" << def.coefs[i];
		}

		out << "x";
		if (sign(def.lits[i])) {
			out << "~";
		}
		out << var(def.lits[i]) << " ";
	}

	switch (def.clause_sign) {
	case big_or_equal_sign:		out << ">="; break;
	case big_sign:				out << "> "; break;
	case small_or_equal_sign:	out << "<="; break;
	case small_sign:			out << "< "; break;
	case equal_sign:			out << "= "; break;
	}

	out << " " << def.clause_const;
	return out;
}

inline std::ostream& operator<<(std::ostream& out, const Clause& cl) {
	for (int i = 0; i < cl.size(); i++) {
		out << cl[i] << " ";
	}
	return out;
}

class DebugHelper {
	std::ostream& out_;

public:
	DebugHelper(std::ostream& out): out_(out) {
	}

	template <class T>
	DebugHelper& operator<<(const T& t) {
		if (false) {
			out_ << t;
		}
		return *this;
	}
};

struct Endl {};
inline std::ostream& operator<<(std::ostream& out, Endl e) {
	out << std::endl;
	return out;
}

}

#endif //Minisat_Debug_h
