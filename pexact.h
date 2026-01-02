/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

#ifndef PEXACT_H
#define PEXACT_H

#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"


#define MAJ_NOBJS 32  // Const0 + Const1 + nVars + nNodes

const int INT_MAX = 2147483647;

const int CONST_ZERO = 0;
const int CONST_ONE = 1;
const int CONST_TWO = 2;
const int CONST_THREE = 3;
const int CONST_FOUR = 4;
const int CONST_FIVE = 5;
const int CONST_SIX = 6;
const int CONST_SEVEN = 7;
const int CONST_TEN = 10;

const int CONST_NINETY_SIX = 96;
const int CONST_FIFTY_SIX = 56;

/**
 * @brief pexact struct.
 *
 * @details
 * Containing SAT solver, starting index of variables and parameters
 *
 * @param pPars Parameters.
 * @param nVars Inputs.
 * @param nNodes Internal nodes.
 * @param nObjs  Total objects (nVars inputs + nNodes internal nodes).
 * @param nWords The truth table size in 64-bit words.
 * @param iVar The next available SAT variable.
 * @param pTruth: Truth table.
 * @param vInfo: nVars + nNodes + 1.
 * @param VarMarks: Variable marks.
 * @param VarVals: Values of the first nVars variables.
 * @param vOutList: Output vars.
 * @param pSat: SAT solver.
 */
typedef struct PexaMan_t_ PexaMan_t;
struct PexaMan_t_ {
    Bmc_EsPar_t * pPars;
    int nVars;
    int nNodes;
    int nObjs;
    int nWords;
    int i_p;            //start of p variables
    int i_o;            //start of o variables
    int o_l;            // amount of o variables
    int i_xo;           //start of output x variables
    int i_mintermvars;  //start of minterm variables
    int iVar;
    int iVarMintermBase;
    word * pTruth;
    Vec_Wrd_t * vInfo;
    int VarMarks[MAJ_NOBJS][2][MAJ_NOBJS];
    int VarVals[MAJ_NOBJS];
    Vec_Wec_t * vOutList;
    sat_solver * pSat;
};
/**
 * @brief Combination element.
 *
 * @details Combination element storing combinations with their internal data.
 *
 * @param act Switching activity.
 * @param r Number of nodes.
 * @param combi Combination array.
 * @param next Pointer to next combination element.
 */
typedef struct Comb_t_ Comb_t;
struct Comb_t_ {
    int act;
    int r;
    int * combi;
    Comb_t * next;
};
/**
 * @brief Combination priority list.
 *
 * @details Combination list storing certain combinations with their internal data.
 *
 * @param start Switching activity.
 * @param len Number of stored combinations.
 * @param length Current length of the list.
 */
typedef struct CombList_t_ CombList_t;
struct CombList_t_ {
    Comb_t * start;
    int len;
    int length;
};

int PowerExactSynthesisBase( Bmc_EsPar_t * pPars );
int PexaManExactPowerSynthesisBasePower( Bmc_EsPar_t * pPars );

#endif
