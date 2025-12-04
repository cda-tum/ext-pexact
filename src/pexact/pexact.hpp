/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

typedef struct Pexa_Man_t_ Pexa_Man_t;
struct Pexa_Man_t_ {
    Bmc_EsPar_t * pPars;                    // parameters
    int nVars;                              // inputs
    int nNodes;                             // internal nodes
    int nObjs;                              // total objects (nVars inputs + nNodes internal nodes)
    int nWords;                             // the truth table size in 64-bit words
    int iVar;                               // the next available SAT variable
    int startPvar;                          //start of p variables
    int startOvar;                          //start of o variables
    int nOvar;                              // amount of o variables
    int startXvar;                          //start of output x variables
    int startMintVars;                      //start of minterm variables
    word * pTruth;                          // truth table
    Vec_Wrd_t * vInfo;                      // nVars + nNodes + 1
    int VarMarks[MAJ_NOBJS][2][MAJ_NOBJS];  // variable marks
    int VarVals[MAJ_NOBJS];                 // values of the first nVars variables
    Vec_Wec_t * vOutList;                   // output vars
    sat_solver * pSat;                      // SAT solver
};
