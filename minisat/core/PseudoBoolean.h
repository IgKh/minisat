/*
 * PseudoBoolean.h
 *
 *  Created on: 12 αιπε 2014
 *      Author: Roey
 */


#ifndef PSEUDOBOOLEAN_H_
#define PSEUDOBOOLEAN_H_

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

#include <iostream>
namespace Minisat {

enum PSConstraintSign { big_or_equal_sign = 0,big_sign=1, small_or_equal_sign = 2,small_sign=3, equal_sign = 4 };

class PSClause{
	public:
	int clause_const;
	PSConstraintSign clause_sign;
	vec<Lit> lits;
	vec<int> coefs;
};

template<class B, class Solver>
static void readPSClause(B& in, Solver& S, PSClause& clause) {
    int     parsed_lit, var,parsed_coef;
    while(*in!=';')
    {
    	while(*in==' ') ++in;
    	//printf("in:%c",*in);
    	switch(*in)
    	{
    	case ';':
    		break;
    	case '>':
    		++in;
    		if(*in == '=')
    		{
    			clause.clause_sign = big_or_equal_sign;
    			++in;
    		}else{clause.clause_sign = big_sign;}
    		clause.clause_const = parseInt(in);
    		break;
    	case '<':
    		++in;
    	    if(*in == '=')
    	    {
    	    	clause.clause_sign = small_or_equal_sign;
    	    	++in;
    	    }else{clause.clause_sign = small_sign;}
    	    clause.clause_const = parseInt(in);
    	    break;
    	case '=':
    		clause.clause_sign = equal_sign;
    		++in;
    		clause.clause_const = parseInt(in);
    		break;
    	default:
    		parsed_coef = parseInt(in);
    		clause.coefs.push(parsed_coef);
    		if(*in==' ') ++in;
    		if(*in=='x') ++in;
    		 parsed_lit = parseInt(in);
    		 if (parsed_lit == 0) break;
    		 var = abs(parsed_lit)-1;
    		 while (var >= S.nVars()) S.newVar();
    		 clause.lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    		 //printf("%d:x%d ",parsed_coef,parsed_lit);
    	}
    }
}

template<class Solver>
static void parse_OPB(gzFile input_stream, Solver& S, bool strictp = false){
	StreamBuffer in(input_stream);
	parse_OPB_main(in, S, strictp);
}

template<class B, class Solver>
static void parse_OPB_main(B& in, Solver& S, bool strictp = false) {
	vec<Lit> lits;
	vec<int> coefs;
	while (*in!=EOF){
	    while ((*in==' ')||(*in=='\n')) ++in;//skip spaces
	    while (*in=='*') skipLine(in);
		if (*in == EOF) break;
		//printf("%c",*in);
		PSClause clause;
		readPSClause(in, S,clause);
        S.addClause(lits);//TODO addPBClause(PSClause clause);
		++in;
	}
	printf("done!");
}
}
#endif /* PSEUDOBOOLEAN_H_ */
