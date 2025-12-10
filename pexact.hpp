/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

#ifndef PEXACT_HPP
#define PEXACT_HPP

#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"

#include <stdio.h>

#define MAJ_NOBJS 32  // Const0 + Const1 + nVars + nNodes
const int CONST_ZERO = 0;
const int CONST_ONE = 1;
const int CONST_TWO = 2;
const int CONST_THREE = 3;
const int CONST_FOUR = 4;
const int CONST_SIX = 6;
const int CONST_TEN = 10;

/*
 * @brief pexact struct.
 *
 * @details
 * Containing SAT solver, starting index of variables and parameters
 *
 *
 */
typedef struct PexaMan_t_ PexaMan_t;
struct PexaMan_t_ {
    Bmc_EsPar_t * pPars;                    // parameters
    int nVars;                              // inputs
    int nNodes;                             // internal nodes
    int nObjs;                              // total objects (nVars inputs + nNodes internal nodes)
    int nWords;                             // the truth table size in 64-bit words
    int iVar;                               // the next available SAT variable
    int i_p;                                //start of p variables
    int i_o;                                //start of o variables
    int o_l;                                // amount of o variables
    int i_xo;                               //start of output x variables
    int i_mintermvars;                      //start of minterm variables
    word * pTruth;                          // truth table
    Vec_Wrd_t * vInfo;                      // nVars + nNodes + 1
    int VarMarks[MAJ_NOBJS][2][MAJ_NOBJS];  // variable marks
    int VarVals[MAJ_NOBJS];                 // values of the first nVars variables
    Vec_Wec_t * vOutList;                   // output vars
    sat_solver * pSat;                      // SAT solver
};

static inline word * PexaManTruth( PexaMan_t * p, int v );
static Vec_Wrd_t * PexaManTruthTables( PexaMan_t * p );
static int PexaManMarkup( PexaMan_t * p );
static PexaMan_t * PexaManAlloc( Bmc_EsPar_t * pPars, word * pTruth );
static void PexaManFree( PexaMan_t * p );
static inline int PexaManFindFanin( PexaMan_t * p, int i, int k );
static inline int PexaManEval( PexaMan_t * p );
int ValueNthBit( int value, int n );
static void PexaManPrintSolution( PexaMan_t * p, int fCompl );
int PexaManGetAct( PexaMan_t * p );
static int AddCnfStart( PexaMan_t * p, int fOnlyAnd );
static int AddCnf( PexaMan_t * p, int iMint );
void PowerExactSynthesisBase( Bmc_EsPar_t * pPars );


#endif
