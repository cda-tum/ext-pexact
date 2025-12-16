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
const int CONST_ZERO = 0;
const int CONST_ONE = 1;
const int CONST_TWO = 2;
const int CONST_THREE = 3;
const int CONST_FOUR = 4;
const int CONST_SIX = 6;
const int CONST_TEN = 10;

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
    int iVar;
    int iVarMintermBase;
    word * pTruth;
    Vec_Wrd_t * vInfo;
    int VarMarks[MAJ_NOBJS][2][MAJ_NOBJS];
    int VarVals[MAJ_NOBJS];
    Vec_Wec_t * vOutList;
    sat_solver * pSat;
};

int PowerExactSynthesisBase( Bmc_EsPar_t * pPars );

#endif
