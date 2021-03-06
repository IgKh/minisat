/*
 * PseudoBoolean.h
 *
 * Parser for OPB format files
 *
 *  Created on: 12 ���� 2014
 *      Author: Roey
 */
#ifndef PSEUDOBOOLEAN_H_
#define PSEUDOBOOLEAN_H_

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

#include <iostream>
namespace Minisat {

template<class B, class Solver>
static void readPbClause(B& in, Solver& S, PbClauseDef& clause) {
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
    		if (parsed_lit == 0)
    			break;

    		var = abs(parsed_lit) - 1;
    		while (var >= S.nVars())
    			S.newVar();

    		clause.lits.push(mkLit(var, parsed_lit < 0));
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

		PbClauseDef clause;
		readPbClause(in, S,clause);
        S.addPbClause(clause);

        ++in;
	}
}
}
#endif /* PSEUDOBOOLEAN_H_ */
