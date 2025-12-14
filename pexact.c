/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

#include "pexact.h"

#include "math.h"
#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"
#include "stdbool.h"
#include "stdio.h"
/**
 * @brief Evaluates truth table pointers.
 *
 * @details Returns pointer to the v'th input truth table using Vec_WrdEntryP.
 *
 * @param p pexact struct.
 * @param v v'th input of the network.
 *
 * @return Word pointer.
 */
static inline word * PexaManTruth( PexaMan_t * p, int v ) { return Vec_WrdEntryP( p->vInfo, p->nWords * v ); }
/**
 * @brief Initialization of truth table variables.
 *
 * @details Initializes p->vInfo and sets Abc_TtIthVar.
 *
 * @param p Pexact struct.
 *
 * @return Vec_Wrd_t pointer to p->vInfo.
 */
static Vec_Wrd_t * PexaManTruthTables( PexaMan_t * p )
{
    p->vInfo = Vec_WrdStart( p->nWords * ( p->nObjs + 1 ) );
    int i;
    for ( i = 0; i < p->nVars; i++ )
    {
        Abc_TtIthVar( PexaManTruth( p, i ), i, p->nVars );
    }
    return p->vInfo;
}
/**
 * @brief Initialization of variables for CNF encoding.
 *
 * @details Initializes all required variables for CNF, including variables for: truth-tables, connectivity, functionality of gates.
 *
 * @param p Pexact struct.
 *
 * @return int as next available free variable.
 */
static int PexaManMarkup( PexaMan_t * p )
{
    int i;
    int k;
    int j;
    assert( p->nObjs <= MAJ_NOBJS );
    // assign functionality
    p->iVar = 1 + ( p->nNodes * CONST_THREE );
    // assign connectivity variables
    for ( i = p->nVars; ( i < p->nObjs ) && ( i < MAJ_NOBJS ) && ( i >= 0 ); i++ )
    {
        for ( k = 0; k < 2; k++ )
        {
            if ( p->pPars->fFewerVars && i == p->nObjs - 1 && k == 0 )
            {
                j = p->nObjs - 2;
                Vec_WecPush( p->vOutList, j, Abc_Var2Lit( p->iVar, 0 ) );
                p->VarMarks[i][k][j] = p->iVar++;
                continue;
            }
            for ( j = p->pPars->fFewerVars ? 1 - k : 0; ( j < ( i - k ) ) && ( j < MAJ_NOBJS ) && ( j >= 0 ); j++ )
            {
                Vec_WecPush( p->vOutList, j, Abc_Var2Lit( p->iVar, 0 ) );
                p->VarMarks[i][k][j] = p->iVar++;
            }
        }
    }
    return p->iVar;
}
/**
 * @brief Allocation pexact struct.
 *
 * @details Allocates all required variables for pexact.
 *
 * @param pPars Terminal input parameters struct from 'pexact -...' command.
 * @param pTruth Truth table word pointer.
 *
 * @return PexaMan_t pointer as allocated pexact struct.
 */
static PexaMan_t * PexaManAlloc( Bmc_EsPar_t * pPars, word * pTruth )
{
    PexaMan_t * p = ABC_CALLOC( PexaMan_t, 1 );
    p->pPars = pPars;
    p->nVars = pPars->nVars;
    p->nNodes = pPars->nNodes;
    p->nObjs = pPars->nVars + pPars->nNodes;
    p->nWords = Abc_TtWordNum( pPars->nVars );
    p->pTruth = pTruth;
    p->vOutList = Vec_WecStart( p->nObjs );
    p->iVar = PexaManMarkup( p );
    p->vInfo = PexaManTruthTables( p );
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, p->iVar );
    return p;
}
/**
 * @brief Deallocation pexact struct.
 *
 * @details Deallocates all previous allocated memory for pexact struct.
 *
 * @param p Pexact struct.
 */
static void PexaManFree( PexaMan_t * p )
{
    sat_solver_delete( p->pSat );
    Vec_WrdFree( p->vInfo );
    Vec_WecFree( p->vOutList );
    ABC_FREE( p );
}
/**
 * @brief Fanin evaluation.
 *
 * @details Determines based on a solution from SAT solver, which fanin a gate has. Return variable indicating the k'th input of gate i
 *
 * @param p Pexact struct.
 * @param i gate i.
 * @param k input k of gate i.
 *
 * @return  variable of input (either fanin or other gate).
 */
static inline int PexaManFindFanin( PexaMan_t * p, int i, int k )
{
    assert( i >= p->nVars && i < p->nObjs && i > 0 );
    assert( i < MAJ_NOBJS );
    assert( k == 0 || k == 1 );


    int j;
    int count = 0;
    int iVar = -1;
    for ( j = 0; ( j < p->nObjs ) && ( j < MAJ_NOBJS ); j++ )
    {
        if ( p->VarMarks[i][k][j] && sat_solver_var_value( p->pSat, p->VarMarks[i][k][j] ) )
        {
            iVar = j;
            count++;
        }
    }
    assert( count == 1 );
    return iVar;
}
/**
 * @brief Evaluation of turth table.
 *
 * @details Determines based on a solution from SAT solver, if the resulting truth-table matches with the specified one. Needed for CEGAR optimizattion approach.
 *          Returns first mismatching minterm.
 *
 * @param p Pexact struct.
 *
 * @return  Index of first mismatching minterm.
 */
static inline int PexaManEval( PexaMan_t * p )
{
    int i;
    int k;
    int iMint;
    word * pFanins[2];
    for ( i = p->nVars; ( i < p->nObjs ) && ( i < MAJ_NOBJS ); i++ )
    {
        const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
        for ( k = 0; k < 2; k++ )
        {
            pFanins[k] = PexaManTruth( p, PexaManFindFanin( p, i, k ) );
        }
        Abc_TtConst0( PexaManTruth( p, i ), p->nWords );
        for ( k = 1; k < 4; k++ )
        {
            if ( !sat_solver_var_value( p->pSat, iVarStart + k - 1 ) )
            {
                continue;
            }
            Abc_TtAndCompl( PexaManTruth( p, p->nObjs ), pFanins[0], ( ( k & 1 ) == 0 ), pFanins[1], ( ( k >> 1 ) == 0 ), p->nWords );
            Abc_TtOr( PexaManTruth( p, i ), PexaManTruth( p, i ), PexaManTruth( p, p->nObjs ), p->nWords );
        }
    }
    iMint = Abc_TtFindFirstDiffBit( PexaManTruth( p, p->nObjs - 1 ), p->pTruth, p->nVars );
    assert( ( p->nVars > 0 ) && ( p->nVars <= CONST_TEN ) );
    assert( iMint < ( 1 << p->nVars ) );
    return iMint;
}
/**
 * @brief Evaluation n'th bit in value for binary representation.
 *
 * @details Determines value of n'th bit of integer value, assuming a binary representation.
 *
 * @param value Binary Integer.
 * @param n n'th bit.
 *
 * @return  Returns either 0 or 1.
 */
static bool ValueNthBit( int value, int n )
{
    return ( value >> n ) & 1;
}
/**
 * @brief Evaluates resulting switching activity.
 *
 * @details Extracting information from solution and calculating overall switching activity of network.
 *
 * @param p Pexact struct.
 *
 * @return  Returns switching activity.
 */
static int PexaManGetAct( PexaMan_t * p )
{
    assert( p->nVars > 0 );
    const int mulPot = 1 << p->nVars;
    const int len = ( p->nObjs ) * mulPot;
    int * xIt = ABC_ALLOC( int, len );
    if ( !xIt )
    {
        printf( "Error: memory allocation failed.\n" );
        return 0;
    }
    const int xiBase = ( p->nNodes * ( 2 * p->nVars + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );
    for ( int i = p->nVars; i < p->nObjs - 1; i++ )
    {
        const int index = i * mulPot;
        xIt[index] = 0;
        for ( int t = 1; t < mulPot; t++ )
        {
            const int innerIndex = ( i * mulPot ) + t;
            xIt[innerIndex] = sat_solver_var_value( p->pSat, xiBase + ( CONST_THREE * ( i - p->nVars + 1 ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) ) );
        }
    }
    int sumAct = 0;
    for ( int i = p->nVars; i < p->nObjs - 1; i++ )
    {
        int sum0 = 0;
        int sum1 = 0;
        int minSum = 0;
        for ( int t = 0; t < mulPot; t++ )
        {
            const int index = ( i * mulPot ) + t;
            if ( xIt[index] == 1 )
            {
                sum1++;
            } else
            {
                sum0++;
            }
        }
        minSum = sum1 <= sum0 ? sum1 : sum0;
        sumAct += 2 * minSum * ( mulPot - minSum );
    }
    ABC_FREE( xIt );
    return sumAct;
}
/**
 * @brief Printing overall truth table.
 *
 * @details Extracting information from solution and printing truth tables.
 *
 * @param p Pexact struct.
 * @param fCompl Parameter indicating if least gate is complemented or not.
 */
static void PexaManPrintSolutionTruthTable( PexaMan_t * p, int fCompl )
{
    if ( p->nObjs >= MAJ_NOBJS )
    {
        printf( "Error: nObjs out of valid range.\n" );
        return;
    }
    printf( "Printing overall Truth Table...\n" );
    assert( p->nVars > 0 );
    const int nTruth = 1 << p->nVars;
    const int len = ( p->nObjs ) * nTruth;
    int * xIt = ABC_ALLOC( int, len );
    if ( !xIt )
    {
        printf( "Error: memory allocation failed.\n" );
        return;
    }
    const int xiBase = ( p->nNodes * ( ( 2 * p->nVars ) + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );

    for ( int i = 0; ( i < p->nVars ) && ( i < p->nObjs ); i++ )
    {
        for ( int t = 0; t < nTruth; t++ )
        {
            const int index = ( i * nTruth ) + t;
            xIt[index] = ValueNthBit( t, i );
        }
    }
    for ( int i = p->nVars; i < p->nObjs - 1; i++ )
    {
        xIt[i * nTruth] = 0;
        for ( int t = 1; t < nTruth; t++ )
        {
            const int index = ( i * nTruth ) + t;
            xIt[index] = sat_solver_var_value( p->pSat, xiBase + ( CONST_THREE * ( i - p->nVars + 1 ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) ) );
        }
    }
    for ( int i = 0; i < p->nObjs - 1; i++ )
    {
        printf( "i=%d:", i );
        for ( int t = 0; t < nTruth; t++ )
        {
            const int index = ( i * nTruth ) + t;
            printf( "%d", xIt[index] );
        }
        printf( "\n" );
    }
    const int iVarStart = 1 + ( CONST_THREE * ( p->nObjs - 1 - p->nVars ) );
    int fOut[CONST_FOUR];
    fOut[CONST_ZERO] = fCompl;
    fOut[CONST_ONE] = fCompl ? ( sat_solver_var_value( p->pSat, iVarStart ) == 0 ) : ( sat_solver_var_value( p->pSat, iVarStart ) );
    fOut[CONST_TWO] = fCompl ? ( sat_solver_var_value( p->pSat, iVarStart + 1 ) == 0 ) : ( sat_solver_var_value( p->pSat, iVarStart + 1 ) );
    fOut[CONST_THREE] = fCompl ? ( sat_solver_var_value( p->pSat, iVarStart + 2 ) == 0 ) : ( sat_solver_var_value( p->pSat, iVarStart + 2 ) );
    const int i0 = PexaManFindFanin( p, p->nObjs - 1, 0 );
    const int i1 = PexaManFindFanin( p, p->nObjs - 1, 1 );
    printf( "i=%d:", p->nObjs - 1 );
    for ( int t = 0; t < nTruth; t++ )
    {
        const int index = ( xIt[( i1 * nTruth ) + t] << 1 ) + ( xIt[( i0 * nTruth ) + t] );
        printf( "%d", fOut[index] );
    }
    ABC_FREE( xIt );
}


/**
 * @brief Printing solution of SAT solver.
 *
 * @details Extracting information from solution and printing connectivity and truth tables.
 *
 * @param p Pexact struct.
 * @param fCompl Parameter indicating if least gate is complemented or not.
 */
static void PexaManPrintSolution( PexaMan_t * p, int fCompl )
{
    int i;
    int k;
    int iVar;

    printf( "Realization of given %d-input function using %d two-input gates complementary=%d:\n", p->nVars, p->nNodes, fCompl );
    for ( i = p->nObjs - 1; ( i >= p->nVars ) && ( i < MAJ_NOBJS ); i-- )
    {
        const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
        const int val1 = sat_solver_var_value( p->pSat, iVarStart );
        const int val2 = sat_solver_var_value( p->pSat, iVarStart + 1 );
        const int val3 = sat_solver_var_value( p->pSat, iVarStart + 2 );
        if ( i == p->nObjs - 1 && fCompl )
        {
            printf( "%02d = 4\'b%d%d%d1(", i, ( val3 == 0 ), ( val2 == 0 ), ( val1 == 0 ) );
        } else
        {
            printf( "%02d = 4\'b%d%d%d0(", i, val3, val2, val1 );
        }

        for ( k = 1; k >= 0; k-- )
        {
            iVar = PexaManFindFanin( p, i, k );
            if ( iVar >= 0 && iVar < p->nVars )
            {
                printf( " %c", 'a' + iVar );
            } else
            {
                printf( " %02d", iVar );
            }
        }
        printf( " )\n" );
    }
    PexaManPrintSolutionTruthTable( p, fCompl );
    printf( "\n" );
    printf( "\n" );
    printf( "Switching Activity=%d\n", PexaManGetAct( p ) );
    printf( "Number of Gates: r=%d\n", p->nNodes );
}
/**
 * @brief Adding Input Uniqueness CNF encoding.
 *
 * @details Adding constraints to encoding that ensure that not two gates exist that use the same two inputs.
 *
 * @param p Pexact struct.
 * @param nList Iteration.
 * @param pList List variables.
 * @param pList2 List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfInpUniq( PexaMan_t * p, int nList, int pList[MAJ_NOBJS], int pList2[2] )
{
    int m = 0;
    int n = 0;
    for ( n = 0; n < nList; n++ )
    {
        for ( m = n + 1; m < nList; m++ )
        {
            pList2[0] = Abc_LitNot( pList[n] );
            pList2[1] = Abc_LitNot( pList[m] );
            if ( !sat_solver_addclause( p->pSat, pList2, pList2 + 2 ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adding symmetry breaking constrains helper.
 *
 * @details Adding constraints to encoding that reduces overall search space. Inner helper function of AddCnfSymBreaking.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param j Iteration variable over all objects(nVars inputs + nNodes internal nodes).
 * @param k Gate input iteration variable.
 * @param pList2 List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfSymBreakingInner( PexaMan_t * p, int i, int j, int k, int pList2[2] )
{
    int n = 0;
    for ( n = j; n < p->nObjs; n++ )
    {
        if ( p->VarMarks[i][k + 1][n] )
        {
            pList2[0] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
            pList2[1] = Abc_Var2Lit( p->VarMarks[i][k + 1][n], 1 );
            if ( !sat_solver_addclause( p->pSat, pList2, pList2 + 2 ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adding symmetry breaking constrains.
 *
 * @details Adding constraints to encoding that reduces overall search space.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param k Gate input iteration variable.
 * @param pList2 List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfSymBreaking( PexaMan_t * p, int i, int k, int pList2[2] )
{
    int j = 0;
    for ( j = 0; j < p->nObjs; j++ )
    {
        if ( p->VarMarks[i][k][j] )
        {
            if ( AddCnfSymBreakingInner( p, i, j, k, pList2 ) == 0 )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adding gate functionality constraints.
 *
 * @details Adding constraints to encoding that ensure that gates only behave as nontrivial operators.
 *
 * @param p Pexact struct.
 * @param fOnlyAnd Least gate is inverted.
 * @param i Gate iteration variable.
 * @param k Gate input iteration variable.
 * @param pList List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfTwoInputFunc( PexaMan_t * p, int fOnlyAnd, int i, int pList[MAJ_NOBJS] )
{
    const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
    int k = 0;
    for ( k = 0; k < CONST_THREE; k++ )
    {
        pList[0] = Abc_Var2Lit( iVarStart, ( k == 1 ) );
        pList[1] = Abc_Var2Lit( iVarStart + 1, ( k == 2 ) );
        pList[2] = Abc_Var2Lit( iVarStart + 2, ( k != 0 ) );
        if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
        {
            return 0;
        }
    }
    if ( fOnlyAnd )
    {
        pList[0] = ( Abc_Var2Lit( iVarStart, 1 ) );
        pList[1] = ( Abc_Var2Lit( iVarStart + 1, 1 ) );
        pList[2] = ( Abc_Var2Lit( iVarStart + 2, 0 ) );
        if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Constrining that every output should be used.
 *
 * @details Adding constraints to encoding that ensure that each output shall be used.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfStartOutUsed( PexaMan_t * p )
{
    int i = 0;
    for ( i = 0; i < p->nObjs - 1; i++ )
    {
        Vec_Int_t * vArray = Vec_WecEntry( p->vOutList, i );

        assert( Vec_IntSize( vArray ) > 0 );
        if ( !sat_solver_addclause( p->pSat, Vec_IntArray( vArray ), Vec_IntLimit( vArray ) ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Inner helper function of PexaManAddCnfStart.
 *
 * @details Inner helper function of PexaManAddCnfStart. Adding all used constraints for each gate i.
 *
 * @param p Pexact struct.
 * @param fOnlyAnd Least gate is inverted.
 * @param i Gate iteration variable.
 * @param pList List variables.
 * @param pList2 List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfStartInner( PexaMan_t * p, int i, int pList[MAJ_NOBJS], int pList2[2], int fOnlyAnd )
{
    int k = 0;
    int j = 0;
    for ( k = 0; k < 2; k++ )
    {
        int nList = 0;
        for ( j = 0; j < p->nObjs; j++ )
        {
            if ( p->VarMarks[i][k][j] )
            {
                pList[nList++] = Abc_Var2Lit( p->VarMarks[i][k][j], 0 );
            }
        }
        assert( nList > 0 );
        // input uniqueness
        if ( !sat_solver_addclause( p->pSat, pList, pList + nList ) )
        {
            return 0;
        }
        if ( AddCnfInpUniq( p, nList, pList, pList2 ) == 0 )
        {
            return 0;
        }
        if ( k == 1 )
        {
            break;
        }
        // symmetry breaking
        if ( AddCnfSymBreaking( p, i, k, pList2 ) == 0 )
        {
            return 0;
        }

        if ( AddCnfTwoInputFunc( p, fOnlyAnd, i, pList ) == 0 )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adding basic constraints for pexact synthesis.
 *
 * @details Iterating over all gates and applying AddCnfStartInner to add all basic constraints.
 *
 * @param p Pexact struct.
 * @param fOnlyAnd Least gate is inverted.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool PexaManAddCnfStart( PexaMan_t * p, int fOnlyAnd )
{
    int pList[MAJ_NOBJS];
    int pList2[2];
    int i = 0;
    // input constraints
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        if ( AddCnfStartInner( p, i, pList, pList2, fOnlyAnd ) == 0 )
        {
            return 0;
        }
    }
    // outputs should be used
    if ( AddCnfStartOutUsed( p ) == 0 )
    {
        return 0;
    }

    return 1;
}
/**
 * @brief Inner function adding fanin connectivity constraints.
 *
 * @details Inner function of AddCnfFaninCon. Constraining which output value a gate i has for which values of input.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param k Truth table iteration variable 0,...,3.
 * @param j All Objects(inputs+gates) iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfFaninConInner( PexaMan_t * p, int i, int k, int j )
{
    int n = 0;
    const int iBaseSatVarI = p->iVar + ( CONST_THREE * ( i - p->nVars ) );
    const int iBaseSatVarJ = p->iVar + ( CONST_THREE * ( j - p->nVars ) );
    for ( n = 0; n < 2; n++ )
    {
        int pList[CONST_THREE];
        int nList = 0;
        pList[nList++] = Abc_Var2Lit( p->VarMarks[i][k][j], 1 );
        pList[nList++] = Abc_Var2Lit( iBaseSatVarI + k, n );
        if ( j >= p->nVars )
        {
            pList[nList++] = Abc_Var2Lit( iBaseSatVarJ + 2, ( n == 0 ) );
        } else if ( p->VarVals[j] == n )
        {
            continue;
        }
        if ( !sat_solver_addclause( p->pSat, pList, pList + nList ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adding fanin connectivity constraints.
 *
 * @details Constraining which output value a gate i has for which values of input.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfFaninCon( PexaMan_t * p, int i )
{
    int k = 0;
    int j = 0;
    for ( k = 0; k < 2; k++ )
    {
        for ( j = 0; j < p->nObjs; j++ )
        {
            if ( p->VarMarks[i][k][j] )
            {
                if ( AddCnfFaninConInner( p, i, k, j ) == 0 )
                {
                    return 0;
                }
            }
        }
    }
    return 1;
}
/**
 * @brief Adding fanin Node functionality helper.
 *
 * @details Helper function for AddCnfNodeFunc functionality constraints.
 *
 * @param p Pexact struct.
 * @param i Minterm iteration variable.
 * @param n Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfNodeFuncInner( PexaMan_t * p, int i, int n )
{
    const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
    const int iBaseSatVarI = p->iVar + ( CONST_THREE * ( i - p->nVars ) );
    int k = 0;
    for ( k = 0; k < 4; k++ )
    {
        int pList[4];
        int nList = 0;
        if ( k == 0 && n == 1 )
        {
            continue;
        }
        pList[nList++] = Abc_Var2Lit( iBaseSatVarI + 0, ( k & 1 ) );
        pList[nList++] = Abc_Var2Lit( iBaseSatVarI + 1, ( k >> 1 ) );
        if ( i != p->nObjs - 1 )
        {
            pList[nList++] = Abc_Var2Lit( iBaseSatVarI + 2, ( n == 0 ) );
        }
        if ( k > 0 )
        {
            pList[nList++] = Abc_Var2Lit( iVarStart + k - 1, n );
        }
        assert( nList <= 4 );
        if ( !sat_solver_addclause( p->pSat, pList, pList + nList ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adding fanin Node functionality constraints.
 *
 * @details Constraining which output value a gate i has depending on the functionality variables(AND,OR,XOR).
 *
 * @param p Pexact struct.
 * @param iMint Minterm iteration variable.
 * @param i Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool AddCnfNodeFunc( PexaMan_t * p, int iMint, int i )
{
    int n = 0;
    const int value = Abc_TtGetBit( p->pTruth, iMint );
    for ( n = 0; n < 2; n++ )
    {
        if ( i == p->nObjs - 1 && n == value )
        {
            continue;
        }
        if ( AddCnfNodeFuncInner( p, i, n ) == 0 )
        {
            return 0;
        }
    }
    return 1;
}
/***
 * @brief Adding hole functionality constraintys for minterm iMint.
 *
 * @details Constraining functionality of logic network for a given minterm iMing.
 *          Including fanin connectivity and gate functionality.
 *
 * @param p Pexact struct.
 * @param iMint Minterm iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static bool PexaManAddCnf( PexaMan_t * p, int iMint )
{
    // save minterm values
    int i = 0;
    // const int value = Abc_TtGetBit( p->pTruth, iMint );
    for ( i = 0; i < p->nVars; i++ )
    {
        p->VarVals[i] = ( iMint >> i ) & 1;
    }
    sat_solver_setnvars( p->pSat, p->iVar + ( CONST_THREE * p->nNodes ) );
    //printf( "Adding clauses for minterm %d with value %d.\n", iMint, Value );
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        // fanin connectivity
        if ( AddCnfFaninCon( p, i ) == 0 )
        {
            return 0;
        }
        // node functionality
        if ( AddCnfNodeFunc( p, iMint, i ) == 0 )
        {
            return 0;
        }
    }

    p->iVar += CONST_THREE * p->nNodes;
    return 1;
}
/**
 * @brief Running exact synthesis.
 *
 * @details Running exact synethesis. Calculating logic network with least amount of gates.
 *          Iterating over gate count r. For each r checking if a solution exists. First solution
 *          corresponds to minimum sized logic network.
 *
 * @param pPars Input information from executed abc command.
 */
int PowerExactSynthesisBase( Bmc_EsPar_t * pPars )
{
    int status;
    int iMint = 1;
    int fCompl = 0;
    word pTruth[16];

    if ( ( pPars->nVars < 2 ) || ( pPars->nVars > CONST_TEN ) )
    {
        printf( "Error: nVars out of valid range (supported: 2..%d).\n", CONST_TEN );
        return 1;
    }

    Abc_TtReadHex( pTruth, pPars->pTtStr );
    const int nWords = Abc_TtWordNum( pPars->nVars );
    if ( pTruth[0] & 1 )
    {
        fCompl = 1;
        Abc_TtNot( pTruth, nWords );
    }


    const int maxNodes = MAJ_NOBJS - pPars->nVars;
    if ( maxNodes <= 0 )
    {
        printf( "Error: too many inputs (%d) for MAJ_NOBJS = %d.\n", pPars->nVars, MAJ_NOBJS );
        return 1;
    }
    for ( int r = 0; r < maxNodes; r++ )
    {
        pPars->nNodes = r + 1;
        PexaMan_t * p = PexaManAlloc( pPars, pTruth );

        status = PexaManAddCnfStart( p, pPars->fOnlyAnd );
        assert( status );
        const int nTruth = 1 << p->nVars;
        bool encoding_failed = false;
        for ( iMint = 1; iMint < nTruth; iMint++ )
        {
            if ( !PexaManAddCnf( p, iMint ) )
            {
                printf( "Error: CNF encoding failed for minterm %d.\n", iMint );
                encoding_failed = true;
                break;
            }
        }
        if ( encoding_failed )
        {
            PexaManFree( p );
            continue;
        }

        status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == 1 )
        {
            PexaManPrintSolution( p, fCompl );
            PexaManFree( p );
            return 0;  // first (minimal) solution found
        }

        PexaManFree( p );
    }

    printf( "No solution found within %d gates.\n", maxNodes );
    return 1;
}
