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
// Cudd BDD library includes after the ABC includes to avoid macro conflicts
#include "bdd/cudd/cudd.h"
#include "bdd/cudd/cuddInt.h"

#include <limits.h>


#define MAJ_NOBJS 32  // Const0 + Const1 + nVars + nNodes

const long long PEXACT_LLONG_MAX = LLONG_MAX;

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

typedef struct MapNpR_t_ MapNpR_t;
struct MapNpR_t_ {
    int n_p;
    int r;
    int var;
};


typedef struct PexaMan_t_ PexaMan_t;
/**
 * @brief pexact struct.
 *
 * @details
 * Containing SAT solver, starting index of variables and parameters
 */
struct PexaMan_t_ {
    /// Parameters
    Bmc_EsPar_t * pPars;
    /// Inputs
    int nVars;
    /// Internal nodes
    int nNodes;
    /// Total objects (nVars inputs + nNodes internal nodes)
    int nObjs;
    /// The truth table size in 64-bit words
    int nWords;
    /// Start of p variables
    int iPVariableStart;
    /// The next available SAT variable
    int iVar;
    /// Start of minterm variables
    int iVarMintermBase;
    /// Truth table.
    word * pTruth;
    /// nVars + nNodes + 1.
    Vec_Wrd_t * vInfo;
    /// Variable marks.
    int VarMarks[MAJ_NOBJS][2][MAJ_NOBJS];
    /// Values of the first nVars variables
    int VarVals[MAJ_NOBJS];
    /// Output vars
    Vec_Wec_t * vOutList;
    /// SAT solver
    sat_solver * pSat;
    /// BDD manager
    DdManager * dd;
    // vector of MapNpR_t
    MapNpR_t * pMap;
    // size of pMap
    int sizeMap;
};


typedef struct Comb_t_ Comb_t;
/**
 * @brief Combination element.
 *
 * @details Combination element storing combinations with their internal data.
 */
struct Comb_t_ {
    /// Switching activity
    int act;
    /// Number of nodes
    int r;
    /// Combination array
    int * combi;
    /// Pointer to next combination element
    Comb_t * next;
};

typedef struct CombList_t_ CombList_t;
/**
 * @brief Combination priority list.
 *
 * @details Combination list storing certain combinations with their internal data.
 */
struct CombList_t_ {
    ///  Pointer to the first combination element in the list.
    Comb_t * start;
    ///  Capacity of the list.
    int len;
    /// Current length of the list.
    int length;
};

/**
 * @brief Helping structure for BDD collection.
 *
 * @details Structure for collecting BDD nodes with their internal data.
 */
typedef struct {
    /// BDD nodes.
    DdNode ** nodes;
    /// node indices.
    int * index;
    /// size of the collection.
    int size;
    /// capacity of the collection.
    int cap;
} BddCollect_t;

int PowerExactSynthesisBase( Bmc_EsPar_t * pPars );
int PexaManExactPowerSynthesisBasePower( Bmc_EsPar_t * pPars );
int PexaManExactPowerSynthesisBasePowerBDD( Bmc_EsPar_t * pPars );
int PexaManExactPowerSynthesisBasePowerBDDBiary( Bmc_EsPar_t * pPars, int stepSize );

#endif
