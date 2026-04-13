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
            for ( j = 0; ( j < ( i - k ) ) && ( j < MAJ_NOBJS ) && ( j >= 0 ); j++ )
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
    p->iVarMintermBase = ( pPars->nNodes * ( 2 * pPars->nVars + pPars->nNodes - 1 ) ) - pPars->nNodes + ( CONST_THREE * pPars->nNodes );
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
    if ( p->pMap != NULL )
    {
        free( p->pMap );
    }
    if ( p->dd != NULL )
    {
        Cudd_Quit( p->dd );
    }
    ABC_FREE( p );
}
/**
 * @brief Fanin evaluation.
 *
 * @details Determines based on a solution from SAT solver, which fanin a gate has. Return variable indicating the k'th input of gate i.
 *
 * @param p Pexact struct.
 * @param i gate i.
 * @param k input k of gate i.
 *
 * @return  variable of input (either fanin or other gate).
 */
static inline int PexaManFindFanin( PexaMan_t * p, const int i, const int k )
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
 * @brief Evaluation of truth table.
 *
 * @details Determines, based on a solution from SAT solver, if the resulting truth-table matches with the specified one. Needed for CEGAR optimization approach.
 *          Returns first mismatching minterm. Function PexaManEval currently not in use.
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
    assert( iMint >= -1 );
    // iMint==-1 -> truth table matches
    return iMint;
}
/**
 * @brief Evaluation n'th bit in value for binary representation.
 *
 * @details Determines value of n'th bit of integer value, assuming a binary representation.
 *
 * @param value Binary integer.
 * @param n n'th bit.
 *
 * @return  Returns either 0 or 1.
 */
static bool ValueNthBit( const int value, const int n )
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
    const int xiBase = p->iVarMintermBase;
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
 * @param bdd  Parameter indicating if BDD p variable encoding is used. Currently unused.
 */
static void PexaManPrintSolutionTruthTable( PexaMan_t * p, const int fCompl, const bool bdd )
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
    int xiBase = p->iVarMintermBase;
    ( void )bdd;  // Currently unused, reserved for future differentiation
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
    printf( "\n" );
    ABC_FREE( xIt );
}
/**
 * @brief Printing solution of SAT solver.
 *
 * @details Extracting information from solution and printing connectivity and truth tables.
 *
 * @param p Pexact struct.
 * @param fCompl Parameter indicating if least gate is complemented or not.
 * @param bdd  Parameter indicating if BDD p variable encoding is used. Currently unused.
 */
static void PexaManPrintSolution( PexaMan_t * p, const int fCompl, const bool bdd )
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
    PexaManPrintSolutionTruthTable( p, fCompl, bdd );
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfInpUniq( PexaMan_t * p, const int nList, const int pList[MAJ_NOBJS], int pList2[2] )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfSymBreakingInner( PexaMan_t * p, const int i, const int j, const int k, int pList2[2] )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfSymBreaking( PexaMan_t * p, const int i, const int k, int pList2[2] )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfTwoInputFunc( PexaMan_t * p, const int fOnlyAnd, const int i, int pList[MAJ_NOBJS] )
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
 * @brief Constraining that every output should be used.
 *
 * @details Adding constraints to encoding that ensure that each output shall be used.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfStartInner( PexaMan_t * p, const int i, int pList[MAJ_NOBJS], int pList2[2], const int fOnlyAnd )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool PexaManAddCnfStart( PexaMan_t * p, const int fOnlyAnd )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfFaninConInner( PexaMan_t * p, const int i, const int k, const int j )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfFaninCon( PexaMan_t * p, const int i )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfNodeFuncInner( PexaMan_t * p, const int i, const int n )
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
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool AddCnfNodeFunc( PexaMan_t * p, const int iMint, const int i )
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
/**
 * @brief Adding hole functionality constraints for minterm iMint.
 *
 * @details Constraining functionality of logic network for a given minterm iMing.
 *          Including fanin connectivity and gate functionality.
 *
 * @param p Pexact struct.
 * @param iMint Minterm iteration variable.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
static bool PexaManAddCnf( PexaMan_t * p, const int iMint )
{
    // save minterm values
    int i = 0;
    for ( i = 0; i < p->nVars; i++ )
    {
        p->VarVals[i] = ( iMint >> i ) & 1;
    }
    sat_solver_setnvars( p->pSat, p->iVar + ( CONST_THREE * p->nNodes ) );
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
 * @details Running exact synthesis. Calculating logic network with least amount of gates.
 *          Iterating over gate count r. For each r checking if a solution exists. First solution
 *          corresponds to minimum sized logic network.
 *
 * @param pPars Input information from executed abc command.
 *
 * @return Returns 0 if synthesis was successful.
 */
int PowerExactSynthesisBase( Bmc_EsPar_t * pPars )
{
    int status;
    int iMint = 1;
    int fCompl = 0;
    word pTruth[16];

    if ( ( pPars->nVars < 2 ) || ( pPars->nVars > CONST_FOUR ) )
    {
        printf( "Error: nVars out of valid range (supported: 2..%d).\n", CONST_FOUR );
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
        bool fEncodingFailed = false;
        if ( !PexaManAddCnfStart( p, pPars->fOnlyAnd ) )
        {
            printf( "Error: CNF base encoding failed.\n" );
            PexaManFree( p );
            continue;  // try next gate count
        }
        const int nTruth = 1 << p->nVars;
        for ( iMint = 1; iMint < nTruth; iMint++ )
        {
            if ( !PexaManAddCnf( p, iMint ) )
            {
                printf( "Error: CNF encoding failed for minterm %d.\n", iMint );
                fEncodingFailed = true;
                break;
            }
        }
        if ( fEncodingFailed )
        {
            PexaManFree( p );
            continue;
        }

        status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == 1 )
        {
            PexaManPrintSolution( p, fCompl, false );
            PexaManFree( p );
            return 0;  // first (minimal) solution found
        }

        PexaManFree( p );
    }

    printf( "No solution found within %d gates.\n", maxNodes );
    return 1;
}
/**
 * @brief Adding and sorting combination to priority list.
 *
 * @details Adding combination to priority list sorted by activity and number of gates.
 *
 * @param act Switching activity.
 * @param r Gate count.
 * @param combi Combinational array.
 * @param list Combination list.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddCombi( const int act, const int r, const int * combi, const int combiLen, CombList_t * list )
{
    int len = list->len;
    if ( len != combiLen )
    {
        printf( "Error: Combination length mismatch.\n" );
        return 0;
    }
    Comb_t * node = ( Comb_t * )malloc( sizeof( Comb_t ) );
    if ( node == NULL )
    {
        return 0;
    }
    node->act = act;
    node->r = r;
    node->combi = ( int * )malloc( len * sizeof( int ) );
    if ( node->combi == NULL )
    {
        free( node );
        return 0;
    }
    node->next = NULL;
    for ( int i = 0; i < len; i++ )
    {
        *( node->combi + i ) = *( combi + i );
    }

    if ( list->length == 0 )
    {
        list->start = node;
    } else
    {
        Comb_t * ptr = list->start;
        if ( ( ptr->act > act ) || ( ( ptr->act == act ) && ( r < ptr->r ) ) )
        {
            list->start = node;
            node->next = ptr;
        } else
        {
            while ( ptr->next != NULL )
            {
                if ( ( ( ptr->act <= act ) && ( ptr->next->act > act ) ) || ( ( ptr->act == act ) && ( ptr->next->act == act ) && ( r >= ptr->r ) && ( r <= ptr->next->r ) ) )
                {
                    node->next = ptr->next;
                    ptr->next = node;
                    list->length++;
                    return 1;
                }
                ptr = ptr->next;
            }
            ptr->next = node;
        }
    }
    // Append at end
    list->length++;
    return 1;
}
/**
 * @brief Remove first element from combination list.
 *
 * @details removing first element from Combination list.
 *
 * @param act Switching activity.
 * @param r Gate count.
 * @param combi Combinational array.
 * @param list Combination list.
 *
 * @return  Returns pointer to removed combination.
 */
Comb_t * PopComb( CombList_t * list )
{
    if ( list->start == NULL )
    {
        return NULL;
    }
    list->length--;
    Comb_t * node = list->start;
    if ( list->start->next != NULL )
    {
        list->start = list->start->next;
    } else
    {
        list->start = NULL;
    }
    return node;
}
/**
 * @brief Deallocate combination list.
 *
 * @details Deallocating all elements in the combination list.
 *
 * @param list Combination list to be deallocated. Will be `free`d.
 */
void FreeCombList( CombList_t * list )
{
    while ( list->length > 0 )
    {
        Comb_t * node = PopComb( list );
        if ( node == NULL )
        {
            break;
        }
        free( node->combi );
        free( node );
    }
}
/**
 * @brief Evaluating P variable values.
 *
 * @details Evaluating P variable values. Iteres over solution from solver and evaluates which p-variables are matching
 *          to cardinallity constraining. Might be used for CEGAR approach. Fimctopm PexaManEvalPVariablesBdd currently
 *          not in use. Similar to PexaManEval.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 *
 * @return Returns -1 if combination matches solution, otherwise returns index of first mismatch.
 */
int PexaManEvalPVariablesBdd( PexaMan_t * p, const int * combi )
{
    int np = pow( 2, p->nVars - 1 ) + 1;
    int combiSol[np];
    for ( int i = 0; i < np; i++ )
    {
        combiSol[i] = 0;
    }

    int mSize = 0;
    for ( int i = 1; i <= pow( 2, p->nVars ) - 1; i++ )
    {
        mSize += i;
    }

    for ( int i = 0; i < p->nNodes - 1; i++ )
    {
        for ( int j = 0; j < np; j++ )
        {
            combiSol[j] += sat_solver_var_value( p->pSat, p->iPVariableStart + ( ( np + mSize ) * i ) + j + mSize );
        }
    }
    for ( int i = 0; i < np - 1; i++ )
    {
        if ( *( combi + i ) != combiSol[i + 1] )
        {
            return i;
        }
    }
    return -1;
}
/**
 * @brief Converting base representation of integer.
 *
 * @details Converting integer to given base representation. Helper function to enumerate all combinations of p-variable
 *          cardinallitys for a given amount of gates r.
 *
 *
 * @example For r=2 gates and k=2 inputs we have to represent integers in base 3.
 *          Amount of combinations is pow( r + 1, pow( 2, k - 1 ) ) = pow( 3, 2 ) = 9
 *          The combinations are:                        {p0,p1}
 *          ConvertBaseInt( 3, 0, 2, results ) results = {0,0}
 *          ConvertBaseInt( 3, 1, 2, results ) results = {1,0}
 *          ConvertBaseInt( 3, 2, 2, results ) results = {2,0}
 *          ConvertBaseInt( 3, 3, 2, results ) results = {0,1}
 *          ConvertBaseInt( 3, 4, 2, results ) results = {1,1}
 *          ConvertBaseInt( 3, 5, 2, results ) results = {2,1}
 *          ...
 *
 * @param base Base.
 * @param value Integer value.
 * @param size Size of the result array.
 * @param results Pointer to result combination array. Results of base conversion are stored here.
 */
void ConvertBaseInt( const int base, int value, const int size, int * results )
{
    int r;
    for ( int i = 0; i < size; i++ )
    {
        r = value % base;
        results[i] = r;
        value = value / base;
    }
}
/**
 * @brief Converting integer to base representation long.
 *
 * @details Converting integer to base representation.
 *          Helper function to enumerate all combinations of p-variable cardinallitys for a given amount of gates r.
 *          Similar to ConvertBaseInt but for long values.
 *
 * @param base Base.
 * @param value long log value.
 * @param size Size of the result array.
 * @param results Pointer to result combination array. Results of base conversion are stored here.
 */
void ConvertBaseIntLong( const int base, long long value, const int size, int * results )
{
    int r;
    for ( int i = 0; i < size; i++ )
    {
        r = value % base;
        results[i] = r;
        value = value / base;
    }
}
/**
 * @brief Adding mux encoding.
 *
 * @details Adds a multiplexer encoding to CNF SAT encoding.
 *
 * @param p Pexact struct.
 * @param o Output variable.
 * @param c Control variable.
 * @param i1 high child.
 * @param i0 low child.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddMuxEncoding( PexaMan_t * p, const int o, const int c, const int i1, const int i0 )
{
    int pList[CONST_THREE];
    pList[CONST_ZERO] = Abc_Var2Lit( c, 1 );
    pList[CONST_ONE] = Abc_Var2Lit( o, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( i1, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 1 );
    pList[CONST_ONE] = Abc_Var2Lit( i1, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( o, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 0 );
    pList[CONST_ONE] = Abc_Var2Lit( o, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( i0, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 0 );
    pList[CONST_ONE] = Abc_Var2Lit( i0, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( o, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    return 1;
}
/**
 * @brief Adding BDD P variable clauses inner function.
 *
 * @details Adds the P variable clauses for BDD encoding to CNF encoding.
 *          Inner function for PexaManAddPClausesBdd. Creates MUX CNF clauses.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param mSize Amount of m variables for BDD.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesBddInner( PexaMan_t * p, const int i, const int mSize, const int xiBase )
{
    int xIt;
    int mStart = p->iVar;
    int np = pow( 2, p->nVars - 1 ) + 1;
    p->iVar += mSize;
    sat_solver_setnvars( p->pSat, p->iVar );
    int pStart = p->iVar;
    p->iVar += np;
    sat_solver_setnvars( p->pSat, p->iVar );
    int lit = Abc_Var2Lit( pStart, 1 );
    if ( !sat_solver_addclause( p->pSat, &lit, &lit + 1 ) )
    {  //restricting p0
        return 0;
    }
    lit = Abc_Var2Lit( mStart, 0 );
    if ( !sat_solver_addclause( p->pSat, &lit, &lit + 1 ) )
    {  //restricting m1 needs to be fulfilled
        return 0;
    }
    int pLen = ( 2 * np ) - 2;
    int * pVars = ( int * )malloc( sizeof( int ) * pLen );
    if ( pVars == NULL )
    {
        return 0;
    }

    memset( pVars, 0, sizeof( int ) * pLen );

    for ( int pi = 0; pi < pLen; ++pi )
    {
        if ( pi < np )
        {
            pVars[pi] = pStart + pi;
        } else
        {
            pVars[pi] = pStart + ( 2 * np ) - 2 - pi;
        }
    }

    int xEnd = ( int )pow( 2, p->nVars ) - 1;
    if ( xEnd < 0 )
    {
        free( pVars );
        return 0;
    }
    int x = 0;
    int y = 0;
    for ( int m = 0; m < mSize; m++ )
    {
        int t = y + x + 1;
        xIt = xiBase + ( CONST_THREE * ( i - p->nVars ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) );
        int m1;
        int m0;
        if ( x == xEnd - 1 && ( y + 1 ) < ( ( 2 * np ) - 2 ) )
        {
            m1 = pVars[y + 1];
            m0 = pVars[y];
        } else
        {
            m1 = mStart + m + xEnd;
            m0 = mStart + m + 1;
        }
        if ( !AddMuxEncoding( p, mStart + m, xIt, m1, m0 ) )
        {
            free( pVars );
            return 0;
        }
        x++;
        if ( x == xEnd )
        {
            x = 0;
            xEnd--;
            y++;
        }
    }
    free( pVars );
    return 1;
}
/**
 * @brief Adding BDD P variable clauses sanity constraints upper bound.
 *
 * @details Adds the P variable clauses for BDD encoding to CNF encoding
 *          Inner function for PexaManAddPClausesBdd. Adds constraints that ensure that excty one p variable of a gate
 *          is fulfilled. Constraints upper bound.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param mSize Amount of m variables for BDD.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesBddSumOneUpper( PexaMan_t * p, const int i, const int j, const int mSize )
{
    int np = pow( 2, p->nVars - 1 ) + 1;
    int litSum = 0;
    int res[np - 1];
    int pList[np - 1];
    ConvertBaseInt( 2, j, np - 1, res );
    int sum = 0;
    for ( int l = 0; l < np - 1; l++ )
    {
        sum += *( res + l );
    }
    if ( sum == 2 )
    {
        litSum = 0;
        for ( int l = 0; l < np - 1; l++ )
        {
            if ( *( res + l ) == 1 )
            {
                pList[litSum++] = Abc_Var2Lit( p->iPVariableStart + ( ( i - p->nVars - 1 ) * ( np + mSize ) ) + mSize + l + 1, 1 );
            }
        }
        if ( !sat_solver_addclause( p->pSat, pList, pList + litSum ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adding BDD P variable clauses sanity constraints lower bound.
 *
 * @details Adds the P variable clauses for BDD encoding to CNF encoding
 *          Inner function for PexaManAddPClausesBdd. Adds constraints that ensure that excty one p variable of a gate
 *          is fulfilled. Constraints lower bound.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param mSize Amount of m variables for BDD.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesBddSumOneLower( PexaMan_t * p, const int i, const int j, const int mSize )
{
    int np = pow( 2, p->nVars - 1 ) + 1;
    int pList[np - 1];

    int litSum = 0;
    int res[np - 1];
    ConvertBaseInt( 2, j, np - 1, res );
    int sum = 0;
    for ( int l = 0; l < np - 1; l++ )
    {
        sum += *( res + l );
    }
    if ( sum == np - 1 )
    {
        litSum = 0;
        for ( int l = 0; l < np - 1; l++ )
        {
            if ( *( res + l ) == 1 )
            {
                pList[litSum++] = Abc_Var2Lit( p->iPVariableStart + ( ( i - p->nVars - 1 ) * ( np + mSize ) ) + mSize + l + 1, 0 );
            }
        }
        if ( !sat_solver_addclause( p->pSat, pList, pList + litSum ) )
        {
            return 0;
        }
    }

    return 1;
}
/**
 * @brief Adding BDD P variable clauses sanity constraints.
 *
 * @details Adds the P variable clauses for BDD encoding to CNF encoding
 *          Inner function for PexaManAddPClausesBdd. Adds constraints that ensure that excty one p variable of a gate
 *          is fulfilled.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable.
 * @param mSize Amount of m variables for BDD.
 *
 * @return @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesBddSumOne( PexaMan_t * p, const int i, const int mSize )
{
    int np = pow( 2, p->nVars - 1 ) + 1;
    for ( int j = 0; j < pow( 2, np - 1 ); j++ )
    {
        if ( !AddPClausesBddSumOneLower( p, i, j, mSize ) )
        {
            return 0;
        }
        if ( !AddPClausesBddSumOneUpper( p, i, j, mSize ) )
        {
            return 0;
        }
    }
    return 1;
}

/**
 * @brief Adding BDD P variable clauses.
 *
 * @details Adds the P variable clauses for BDD encoding to CNF encoding.
 *
 * @param p Pexact struct.
 *
 * @return @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddPClausesBdd( PexaMan_t * p )
{
    int xiBase = ( p->nNodes * ( ( 2 * p->nVars ) + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );
    int mSize = pow( 2, p->nVars ) - 1;
    int fak = 0;
    int np = pow( 2, p->nVars - 1 ) + 1;

    for ( int f = 1; f <= mSize; f++ )
    {
        fak = fak + f;
    }
    mSize = fak;
    p->iPVariableStart = p->iVar;
    // reserverve space for mSize * p->nNodes entries
    int numElements = mSize * ( p->nNodes - 1 );
    if ( numElements <= 0 )
    {
        printf( "Error: Map size is non-positive. mSize: %d, nNodes: %d\n", mSize, p->nNodes );
        return 0;
    }
    p->sizeMap = np * ( p->nNodes - 1 );
    p->pMap = ( MapNpR_t * )malloc( sizeof( MapNpR_t ) * p->sizeMap );
    if ( p->pMap == NULL )
    {
        printf( "Error: Memory allocation failed for pMap.\n" );
        return 0;
    }
    memset( p->pMap, 0, sizeof( MapNpR_t ) * p->sizeMap );
    for ( int i = p->nVars + 1; i < p->nVars + p->nNodes; i++ )
    {
        for ( int l = 0; l < np - 1; l++ )
        {
            int idx = ( ( np - 1 ) * ( i - p->nVars - 1 ) ) + l;
            if ( idx < p->sizeMap )
            {
                p->pMap[idx].var = p->iPVariableStart + ( ( i - p->nVars - 1 ) * ( np + mSize ) ) + mSize + l + 1;
                p->pMap[idx].n_p = l + 1;
                p->pMap[idx].r = i - p->nVars - 1;
            }
        }
        if ( !AddPClausesBddInner( p, i, mSize, xiBase ) )
        {
            return 0;
        }
        if ( !AddPClausesBddSumOne( p, i, mSize ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Calculating maximum switching activity.
 *
 * @details Calculates the maximum switching activity for a given gate count and input size.
 *
 * @param r Gate count.
 * @param k Primary input count.
 *
 * @return Returns maximum switching activity.
 */
int CalcMaxAct( const int r, const int k )
{
    int ret = 0;
    if ( k == 4 )
    {
        int rRest = r - 2;
        ret = ( rRest * ( ( pow( 2, k + 1 ) - 2 ) ) ) + CONST_NINETY_SIX + CONST_FIFTY_SIX;
    } else
    {
        ret = ( int )( ( ( pow( 2, k + 1 ) - 2 ) ) * r );
    }
    return ret;
}
/**
 * @brief Evaluate k=4 restrictions.
 *
 * @details Calculates all combinations of switching activities for a given gate count and input size.
 *
 * @param res Combinational array.
 *
 * @return Returns 1 if restriction applies.
 */
bool EvaluateRestrictions4( const int * res, const int resLen )
{
    if ( resLen <= CONST_SEVEN )
    {
        return false;
    }
    int p2 = *( res + CONST_ONE );
    int p4 = *( res + CONST_THREE );
    int p6 = *( res + CONST_FIVE );
    int p8 = *( res + CONST_SEVEN );
    bool feasible = ( p4 >= 2 ) | ( p8 >= 2 ) | ( ( p4 >= 1 ) && ( p8 >= 1 ) ) | ( ( ( p4 >= 1 ) | ( p8 >= 1 ) ) && ( ( p2 >= 1 ) | ( p6 >= 1 ) ) );
    if ( feasible )
    {
        return 1;
    }
    return 0;
}

/**
 * @brief Calculating combinational list for given r.
 *
 * @details Calculates all combinations of switching activities for a given gate count and input size.
 *
 * @param k Primary input count.
 * @param r Gate count.
 * @param list Combination list.
 *
 * @return Returns status.
 * @retval true if adding insertion succeeded.
 * @retval false if adding insertion failed.
 */
bool CalculateCombArray( const int k, const int r, CombList_t * list )
{
    if ( r == 0 )
    {
        return 0;
    }
    // Check for potential overflow in size calculation
    double sizeD = pow( r + 1, pow( 2, k - 1 ) );
    if ( sizeD > PEXACT_LLONG_MAX || sizeD < 0 )
    {
        printf( "Error: Combination array size exceeds limits for r=%d, k=%d.\n", r, k );
        return 0;
    }
    long long size = pow( r + 1, pow( 2, k - 1 ) );
    int sizeSingle = pow( 2, k - 1 );
    int arraySingle[sizeSingle];
    for ( int i = 0; i < sizeSingle; i++ )
    {
        arraySingle[i] = 2 * ( i + 1 ) * ( pow( 2, k ) - ( i + 1 ) );
    }
    for ( long long i = 0; i < size; i++ )
    {
        int res[sizeSingle];
        ConvertBaseIntLong( r + 1, i, sizeSingle, res );
        int sum = 0;
        int sumAct = 0;
        for ( int j = 0; j < sizeSingle; j++ )
        {
            sum += *( res + j );
            sumAct += arraySingle[j] * ( *( res + j ) );
            if ( sum > r )
            {
                j = sizeSingle;
            }
        }

        if ( sum != r )
        {
            continue;
        }

        if ( k == 4 )
        {
            if ( EvaluateRestrictions4( res, sizeSingle ) )
            {
                if ( !AddCombi( sumAct, r, res, sizeSingle, list ) )
                {
                    return 0;
                }
            }
        } else
        {
            if ( !AddCombi( sumAct, r, res, sizeSingle, list ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Cardinality constraints insertion lower bound.
 *
 * @details Inserts cardinality constraints for a given combination into CNF encoding, using polynomial cardinality
 *          constraints. Lower bound.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddCardinalityLower( PexaMan_t * p, const int * combi, const int xp )
{
    int ni = p->nNodes - 1;
    int np = pow( 2, p->nVars - 1 );
    int pi = xp;
    int pList[ni];
    int lit = 0;
    int l = *( combi + pi );
    // less then l
    int j = l + 1;
    for ( int i = 0; i < pow( 2, ni ); i++ )
    {
        int res[ni];
        ConvertBaseInt( 2, i, ni, res );
        int sum = 0;
        for ( int li = 0; li < ni; li++ )
        {
            sum += *( res + li );
        }
        if ( sum == j )
        {
            lit = 0;
            for ( int l = 0; l < ni; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[lit++] = Abc_Var2Lit( p->iPVariableStart + ( l * np ) + pi, 1 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + lit ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Cardinality constraints insertion upper bounds.
 *
 * @details Inserts cardinality constraints for a given combination into CNF encoding, using polynomial cardinality
 *          constraints. Upper bound.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddCardinalityUpper( PexaMan_t * p, const int * combi, const int xp )
{
    int ni = p->nNodes - 1;
    int np = pow( 2, p->nVars - 1 );
    int pi = xp;
    int pList[ni];
    int lit = 0;
    int l = *( combi + pi );
    // more then l
    int j = ni - l + 1;
    for ( int i = 0; i < pow( 2, ni ); i++ )
    {
        int res[ni];
        ConvertBaseInt( 2, i, ni, res );
        int sum = 0;
        for ( int l = 0; l < ni; l++ )
        {
            sum += *( res + l );
        }
        if ( sum == j )
        {
            lit = 0;
            for ( int l = 0; l < ni; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[lit++] = Abc_Var2Lit( p->iPVariableStart + ( l * np ) + pi, 0 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + lit ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Cardinality constraints insertion.
 *
 * @details Inserts cardinality constraints for a given combination into CNF encoding, using polynomial cardinality constraints.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddCardinality( PexaMan_t * p, const int * combi, const int xp )
{
    if ( !PexaManAddCardinalityLower( p, combi, xp ) )
    {
        return 0;
    }
    if ( !PexaManAddCardinalityUpper( p, combi, xp ) )
    {
        return 0;
    }
    return 1;
}
/**
 * @brief Returns minimum of (one-bits count, zero-bits count + 1).
 *
 * @details Used for indexing pListP array. Caller typically subtracts 1 from result.
 *
 * @param value Decimal value.
 * @param len Length of binary representation.
 *
 * @return min(one-bits, zero-bits + 1).
 */
int CountOne( int value, const int len )
{
    int ret1 = 0;
    int ret0 = 1;
    for ( int i = 0; i < len; i++ )
    {
        ret1 += value & 1;
        ret0 += !( value & 1 );
        value >>= 1;
    }
    return ret0 >= ret1 ? ret1 : ret0;
}
/**
 * @brief Adds naive p variable encoding inner function.
 *
 * @details Introduces naive p variable encoding to SAT CNF encoding. Helper function of PexaManAddPClauses.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesInner( PexaMan_t * p, const int i )
{
    int pStartvar = p->iVar;
    int xiBase = ( p->nNodes * ( ( 2 * p->nVars ) + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );
    int litsize = pow( 2, p->nVars );
    int np = pow( 2, p->nVars - 1 );
    int nCombs = pow( 2, pow( 2, p->nVars ) - 1 );
    int pList[litsize];
    int pListP[np];
    int xIt = 0;
    int pTarget = 0;
    p->iVar += np;  // Reserve SAT variables for this gate
    sat_solver_setnvars( p->pSat, p->iVar );
    for ( int pi = 0; pi < np; pi++ )
    {
        pListP[pi] = Abc_Var2Lit( pStartvar++, 0 );
    }

    for ( int m = 1; m < nCombs; m++ )
    {
        for ( int t = 1; t < pow( 2, p->nVars ) && t <= litsize; t++ )
        {
            xIt = xiBase + ( CONST_THREE * ( i - p->nVars ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) );
            pList[t - 1] = Abc_Var2Lit( xIt, ValueNthBit( m, t - 1 ) );
        }
        pTarget = CountOne( m, litsize - 1 ) - 1;
        if ( pTarget < 0 || pTarget >= np )
        {
            return 0;
        }
        pList[litsize - 1] = pListP[pTarget];
        if ( !sat_solver_addclause( p->pSat, pList, pList + litsize ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adds naive p variable encoding lower bound.
 *
 * @details Introduces naive p variable encoding to SAT CNF encoding. Helper function of PexaManAddPClauses.
 *          Ensures that only one p variable is satisfied.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesSumOneLower( PexaMan_t * p, const int i )
{
    int litsize = pow( 2, p->nVars );
    int np = pow( 2, p->nVars - 1 );
    int pList[litsize];
    for ( int j = 0; j < pow( 2, np ); j++ )
    {
        int litSum = 0;
        int res[np];
        ConvertBaseInt( 2, j, np, res );
        int sum = 0;
        for ( int l = 0; l < np; l++ )
        {
            sum += *( res + l );
        }
        if ( sum == 2 )
        {
            litSum = 0;
            for ( int l = 0; l < np; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[litSum++] = Abc_Var2Lit( p->iPVariableStart + ( ( i - p->nVars - 1 ) * np ) + l, 1 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + litSum ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adds naive p variable encoding upper bound.
 *
 * @details Introduces naive p variable encoding to SAT CNF encoding. Helper function of PexaManAddPClauses.
 *          Ensures that only one p variable is satisfied.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesSumOneUpper( PexaMan_t * p, const int i )
{
    int litsize = pow( 2, p->nVars );
    int np = pow( 2, p->nVars - 1 );
    int pList[litsize];
    for ( int j = 0; j < pow( 2, np ); j++ )
    {
        int litSum = 0;
        int res[np];
        ConvertBaseInt( 2, j, np, res );
        int sum = 0;
        for ( int l = 0; l < np; l++ )
        {
            sum += *( res + l );
        }
        if ( sum == np )
        {
            litSum = 0;
            for ( int l = 0; l < np; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[litSum++] = Abc_Var2Lit( p->iPVariableStart + ( ( i - p->nVars - 1 ) * np ) + l, 0 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + litSum ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adds naive p variable encoding.
 *
 * @details Introduces naive p variable encoding to SAT CNF encoding. Helper function of PexaManAddPClauses.
 *          Ensures that only one p variable is satisfied.
 *
 * @param p Pexact struct.
 * @param i Gate iteration variable
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddPClausesSumOne( PexaMan_t * p, const int i )
{
    if ( !AddPClausesSumOneLower( p, i ) )
    {
        return 0;
    }
    if ( !AddPClausesSumOneUpper( p, i ) )
    {
        return 0;
    }
    return 1;
}
/**
 * @brief Adds naive p variable encoding.
 *
 * @details Introduces naive p variable encoding to SAT CNF encoding.
 *
 * @param p Pexact struct.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddPClauses( PexaMan_t * p )
{
    p->iPVariableStart = p->iVar;
    for ( int i = p->nVars + 1; i < p->nVars + p->nNodes; i++ )
    {
        if ( !AddPClausesInner( p, i ) )
        {
            return 0;
        }
        if ( !AddPClausesSumOne( p, i ) )
        {
            return 0;
        }
    }
    return 1;
}
/**
 * @brief Adds carinality constraints.
 *
 * @details Introduces cardinality constraints for BDD type encoding for p variables to SAT CNF encoding.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddCardinalityBddLower( PexaMan_t * p, const int * combi, const int xp )
{
    int ni = p->nNodes - 1;
    int np = pow( 2, p->nVars - 1 ) + 1;
    int mLen = 0;
    for ( int i = 1; i <= pow( 2, p->nVars ) - 1; i++ )
    {
        mLen += i;
    }
    int pi = xp;
    int pList[ni];
    int lit = 0;
    int l = *( combi + pi );
    // less then l
    int j = l + 1;
    for ( int i = 0; i < pow( 2, ni ); i++ )
    {
        int res[ni];
        ConvertBaseInt( 2, i, ni, res );
        int sum = 0;
        for ( int l = 0; l < ni; l++ )
        {
            sum += *( res + l );
        }
        if ( sum == j )
        {
            lit = 0;
            for ( int l = 0; l < ni; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[lit++] = Abc_Var2Lit( p->iPVariableStart + mLen + ( l * ( mLen + np ) ) + pi + 1, 1 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + lit ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adds carinality constraints.
 *
 * @details Introduces cardinality constraints for BDD type encoding for p variables to SAT CNF encoding.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool AddCardinalityBddUpper( PexaMan_t * p, const int * combi, const int xp )
{
    int ni = p->nNodes - 1;
    int np = pow( 2, p->nVars - 1 ) + 1;
    int mLen = 0;
    for ( int i = 1; i <= pow( 2, p->nVars ) - 1; i++ )
    {
        mLen += i;
    }
    int pi = xp;
    int pList[ni];
    int lit = 0;
    int l = *( combi + pi );
    int j = ni - l + 1;
    for ( int i = 0; i < pow( 2, ni ); i++ )
    {
        int res[ni];
        ConvertBaseInt( 2, i, ni, res );
        int sum = 0;
        for ( int l = 0; l < ni; l++ )
        {
            sum += *( res + l );
        }
        if ( sum == j )
        {
            lit = 0;
            for ( int l = 0; l < ni; l++ )
            {
                if ( *( res + l ) == 1 )
                {
                    pList[lit++] = Abc_Var2Lit( p->iPVariableStart + mLen + ( l * ( mLen + np ) ) + pi + 1, 0 );
                }
            }
            if ( !sat_solver_addclause( p->pSat, pList, pList + lit ) )
            {
                return 0;
            }
        }
    }
    return 1;
}
/**
 * @brief Adds carinality constraints.
 *
 * @details Introduces cardinality constraints for BDD type encoding for p variables to SAT CNF encoding.
 *
 * @param p Pexact struct.
 * @param combi Combinational array.
 * @param xp Iteration variable of p variables.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool PexaManAddCardinalityBdd( PexaMan_t * p, const int * combi, const int xp )
{
    if ( !AddCardinalityBddLower( p, combi, xp ) )
    {
        return 0;
    }
    if ( !AddCardinalityBddUpper( p, combi, xp ) )
    {
        return 0;
    }
    return 1;
}
/**
 * @brief Adds CNF Encoding.
 *
 * @details Introduces all essecary CNF Constraints into the SAT Solver.
 *
 * @param pPars Input information from executed abc command.
 * @param p Pexact struct.
 * @param node Combinational node.
 * @param list Combinational list.
 *
 * @return Returns status.
 * @retval true if adding encoding succeeded.
 * @retval false if adding encoding failed.
 */
bool ExactPowerSynthesisCNF( Bmc_EsPar_t * pPars, PexaMan_t * p, Comb_t * node, CombList_t * list )
{
    if ( !PexaManAddCnfStart( p, pPars->fOnlyAnd ) )
    {
        return 0;
    }
    for ( int iMint = 1; iMint < pow( 2, p->nVars ); iMint++ )
    {
        if ( !PexaManAddCnf( p, iMint ) )
        {
            return 0;
        }
    }
    if ( !PexaManAddPClausesBdd( p ) )
    {
        return 0;
    }
    for ( int i0 = 0; i0 < list->len; i0++ )
    {
        if ( !PexaManAddCardinalityBdd( p, node->combi, i0 ) )
        {
            return 0;
        }
    }
    return 1;
}

/**
 * @brief Builds a BDD for the constraint "exactly n out of r are active" (optimized variant).
 *
 * @details Enumerates all binary assignments of length r, selects those with Hamming weight n,
 *          builds one conjunction per valid assignment, and combines them with OR.
 *          Variables are mapped with offset np and stride nP.
 *
 * @param manager CUDD manager.
 * @param n Required number of active variables.
 * @param r Number of variables in the group.
 * @param np Offset of the p-variable class.
 * @param nP Total number of p-variable classes per gate.
 *
 * @return Pointer to resulting BDD node (referenced).
 */
DdNode * BddNOutofROptCudd( DdManager * dd, int n, int r, int np, int nP )
{
    int * comb = ( int * )malloc( sizeof( int ) * r );
    if ( comb == NULL )
    {
        free( comb );
        return Cudd_ReadLogicZero( dd );
    }
    int nCombs = pow( 2, r );

    // Init Cudd database
    DdNode * o = Cudd_ReadLogicZero( dd );
    Cudd_Ref( o );


    for ( int i = 0; i < nCombs; i++ )
    {
        ConvertBaseInt( 2, i, r, comb );
        int sum = 0;
        for ( int nR = 0; nR < r; nR++ )
        {
            sum += comb[nR];
        }

        if ( sum == n )
        {
            DdNode * andNode = Cudd_ReadOne( dd );
            Cudd_Ref( andNode );


            for ( int nR = 0; nR < r; nR++ )
            {
                if ( comb[nR] != 0 )
                {
                    // Variable holen (CUDD braucht hier kein Ref, wenn direkt genutzt,
                    // aber wir machen es für die Logik konsistent)
                    DdNode * var = Cudd_bddIthVar( dd, ( nR * nP ) + np );
                    Cudd_Ref( var );

                    DdNode * tmpAnd = Cudd_bddAnd( dd, andNode, var );
                    Cudd_Ref( tmpAnd );

                    // Alte Referenzen aufräumen
                    Cudd_RecursiveDeref( dd, andNode );
                    Cudd_RecursiveDeref( dd, var );

                    andNode = tmpAnd;
                }
            }

            // Jetzt das Ergebnis der AND-Kette mit dem globalen OR verknüpfen
            DdNode * tmpOr = Cudd_bddOr( dd, o, andNode );
            Cudd_Ref( tmpOr );

            Cudd_RecursiveDeref( dd, o );
            Cudd_RecursiveDeref( dd, andNode );

            o = tmpOr;
        }
    }
    free( comb );
    return o;
}


/**
 * @brief Builds a BDD for the constraint "exactly n out of r are active".
 *
 * @details Enumerates all binary assignments of length r, constructs one product term
 *          (including positive/negative phases) for each assignment with Hamming weight n,
 *          and accumulates all terms with OR.
 *
 * @param dd CUDD manager.
 * @param n Required number of active variables.
 * @param r Number of variables in the group.
 * @param np Offset of the p-variable class.
 * @param nP Total number of p-variable classes per gate.
 *
 * @return Pointer to resulting BDD node (referenced).
 */
DdNode * BddNOutofRCudd( DdManager * dd, int n, int r, int np, int nP )
{
    int * comb = ( int * )malloc( sizeof( int ) * r );
    if ( comb == NULL )
    {
        return Cudd_ReadLogicZero( dd );
    }
    int nCombs = ( int )pow( 2, r );

    DdNode * o = Cudd_ReadLogicZero( dd );
    Cudd_Ref( o );

    for ( int i = 0; i < nCombs; i++ )
    {
        // Generate combination for current iteration
        ConvertBaseInt( 2, i, r, comb );

        int sum = 0;
        for ( int nR = 0; nR < r; nR++ )
        {
            sum += comb[nR];
        }

        // IF sum of current combination equals n
        if ( sum == n )
        {
            // Initialisierung des AND-Pfades mit der ersten Variable
            int firstIdx = np;
            DdNode * var = Cudd_bddIthVar( dd, firstIdx );
            DdNode * andNode = ( comb[0] == 0 ) ? Cudd_Not( var ) : var;
            Cudd_Ref( andNode );

            // Verknüpfung der restlichen r-1 Variable
            for ( int nR = 1; nR < r; nR++ )
            {
                int currentIdx = ( nR * nP ) + np;
                DdNode * nextVar = Cudd_bddIthVar( dd, currentIdx );
                DdNode * phaseVar = ( comb[nR] == 0 ) ? Cudd_Not( nextVar ) : nextVar;

                DdNode * tmp = Cudd_bddAnd( dd, andNode, phaseVar );
                Cudd_Ref( tmp );
                Cudd_RecursiveDeref( dd, andNode );
                andNode = tmp;
            }

            // Valid AND-Chain combined with global OR
            DdNode * tmpOr = Cudd_bddOr( dd, o, andNode );
            Cudd_Ref( tmpOr );
            Cudd_RecursiveDeref( dd, o );
            Cudd_RecursiveDeref( dd, andNode );
            o = tmpOr;
        }
    }

    free( comb );
    return o;
}


/**
 * @brief Computes BDD for activity window and excludes all-zero assignment.
 *
 * @details Enumerates all p-variable cardinality combinations for given gate count r,
 *          keeps combinations with total activity in [actMin, act] and exact gate usage,
 *          builds corresponding BDD terms, OR-combines them, and finally ANDs with a
 *          "not-all-zero" condition over all involved BDD variables.
 *
 * @param dd CUDD manager.
 * @param p Pexact struct.
 * @param r Gate count used in combination enumeration.
 * @param act Upper activity bound.
 * @param actMin Lower activity bound.
 *
 * @return Pointer to resulting BDD node (referenced).
 */
DdNode * CalculateBddCuddSmallerThanMin(
    DdManager * dd,
    PexaMan_t * p,
    int r,
    int act,
    int actMin )
{
    int k = p->nVars;
    int nP = ( int )pow( 2, k - 1 );
    int * wP = ( int * )malloc( sizeof( int ) * nP );
    int * combi = ( int * )malloc( sizeof( int ) * nP );

    int sats = 0;
    DdNode * orNode = Cudd_ReadLogicZero( dd );
    Cudd_Ref( orNode );

    for ( int i = 0; i < nP; i++ )
    {
        wP[i] = 2 * ( i + 1 ) * ( ( int )pow( 2, k ) - ( i + 1 ) );
    }

    int combs = ( int )pow( r + 1, nP );

    // 1. Main loop: Enumerate all combinations of p-variable assignments
    for ( int c = 0; c < combs; c++ )
    {
        int sum = 0;
        int sumB = 0;
        ConvertBaseInt( r + 1, c, nP, combi );

        for ( int j = 0; j < nP; j++ )
        {
            sumB += combi[j];
            sum += wP[j] * combi[j];
        }

        if ( sum <= act && sum >= actMin && sumB == r )
        {
            sats++;
            DdNode * andNode = Cudd_ReadOne( dd );
            Cudd_Ref( andNode );

            for ( int i = 0; i < nP; i++ )
            {
                if ( combi[i] != 0 )
                {
                    DdNode * tmp = BddNOutofROptCudd( dd, combi[i], r, i, nP );
                    if ( tmp == Cudd_ReadLogicZero( dd ) )
                    {
                        printf( "CRITICAL ERROR\n" );
                        free( combi );
                        free( wP );
                        return Cudd_ReadLogicZero( dd );
                    }
                    Cudd_Ref( tmp );
                    DdNode * nextAnd = Cudd_bddAnd( dd, andNode, tmp );
                    Cudd_Ref( nextAnd );
                    Cudd_RecursiveDeref( dd, andNode );
                    Cudd_RecursiveDeref( dd, tmp );
                    andNode = nextAnd;
                }
            }
            DdNode * nextOr = Cudd_bddOr( dd, orNode, andNode );
            Cudd_Ref( nextOr );
            Cudd_RecursiveDeref( dd, orNode );
            Cudd_RecursiveDeref( dd, andNode );
            orNode = nextOr;
        }
    }

    free( combi );
    free( wP );

    Cudd_RecursiveDeref( dd, orNode );

    return orNode;
}

/**
 * @brief Adds MUX encoding clauses without explicit error propagation.
 *
 * @details Inserts the four standard CNF clauses for o = (c ? i1 : i0) into the SAT solver.
 *          This helper variant does not return a status and assumes clause insertion succeeds.
 *
 * @param p Pexact struct.
 * @param o Output variable.
 * @param c Control variable.
 * @param i1 High child variable.
 * @param i0 Low child variable.
 */
bool AddMuxEncodingCudd( PexaMan_t * p, int o, int c, int i1, int i0 )
{
    int pList[CONST_THREE];
    pList[CONST_ZERO] = Abc_Var2Lit( c, 1 );
    pList[CONST_ONE] = Abc_Var2Lit( o, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( i1, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 1 );
    pList[CONST_ONE] = Abc_Var2Lit( i1, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( o, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 0 );
    pList[CONST_ONE] = Abc_Var2Lit( o, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( i0, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    pList[CONST_ZERO] = Abc_Var2Lit( c, 0 );
    pList[CONST_ONE] = Abc_Var2Lit( i0, 1 );
    pList[CONST_TWO] = Abc_Var2Lit( o, 0 );
    if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
    {
        return 0;
    }
    return 1;
}


/**
 * @brief Visits one BDD child and appends it to the collection if needed.
 *
 * @details Normalizes the child pointer, skips constants and already seen nodes,
 *          and adds the node to the collection if capacity allows.
 *
 * @param child BDD child node.
 * @param c BDD node collection.
 *
 * @return Returns node position in the collection.
 * @retval >= 0 if the child was added successfully.
 * @retval -1 if the child is constant or already present.
 * @retval -2 if the collection capacity is exceeded.
 */

static int VisitChild( DdNode * child, BddCollect_t * c )
{
    child = Cudd_Regular( child );
    if ( Cudd_IsConstant( child ) )
    {
        return -1;
    }

    // Search for existing nodes
    for ( int i = 0; i < c->size; i++ )
    {
        if ( c->nodes[i] == child )
        {
            return -1;
        }
    }

    // Add children
    if ( c->size >= c->cap )
    {
        printf( "CRITICAL ERROR\n" );
        return -2;
    }

    c->nodes[c->size] = child;
    c->index[c->size] = 0;
    int newPos = c->size;
    c->size++;

    return newPos;
}

/**
 * @brief Iteratively collects all reachable BDD nodes.
 *
 * @details Traverses the BDD starting at the root and stores each visited node
 *          exactly once in the collection.
 *
 * @param f BDD root node.
 * @param c BDD node collection.
 */
static void CollectIter( DdNode * f, BddCollect_t * c )
{
    f = Cudd_Regular( f );
    if ( Cudd_IsConstant( f ) )
    {
        return;
    }

    c->nodes[0] = f;
    c->index[0] = 0;
    c->size = 1;
    int cur = 0;

    while ( cur >= 0 )
    {
        DdNode * node = c->nodes[cur];

        if ( c->index[cur] == 0 )
        {
            c->index[cur] = 1;
            int next = VisitChild( Cudd_T( node ), c );
            if ( next >= 0 )
            {
                cur = next;
            }
        } else if ( c->index[cur] == 1 )
        {
            c->index[cur] = 2;
            int next = VisitChild( Cudd_E( node ), c );
            if ( next >= 0 )
            {
                cur = next;
            }
        } else
        {
            cur--;
        }
    }
}

/**
 * @brief Adds one BDD-derived cardinality clause for a single collected node.
 *
 * @details Encodes the selected BDD node as a MUX-style SAT clause using the
 *          mapped node variable and the constant literals.
 *
 * @param p Pexact struct.
 * @param col BDD node collection.
 * @param nodeVar SAT variable mapping for collected nodes.
 * @param i Node index in the collection.
 * @param litConst0Raw Raw SAT variable for constant 0.
 * @param litConst1Raw Raw SAT variable for constant 1.
 */
bool ExaManAddCardClausesCuddInner( PexaMan_t * p, BddCollect_t * col, const int * nodeVar, int i, int litConst0Raw, int litConst1Raw )
{
    DdNode * node = col->nodes[i];
    int nodeIdx = node->index;

    int pi = 0;
    if ( nodeIdx < p->sizeMap && p->pMap != NULL && nodeIdx >= 0 )
    {
        pi = p->pMap[nodeIdx].var;
    }

    DdNode * nodeT = Cudd_E( node );
    DdNode * nodeE = Cudd_T( node );
    int child0 = -CONST_THREE;
    int child1 = -CONST_THREE;
    for ( int j = 0; j < col->size; j++ )
    {
        if ( col->nodes[j] == nodeT )
        {
            child1 = nodeVar[j];
        }
        if ( col->nodes[j] == nodeE )
        {
            child0 = nodeVar[j];
        }
    }
    if ( Cudd_ReadLogicZero( p->dd ) == nodeT )
    {
        child1 = litConst0Raw;
    } else if ( Cudd_ReadOne( p->dd ) == nodeT )
    {
        child1 = litConst1Raw;
    }
    if ( Cudd_ReadLogicZero( p->dd ) == nodeE )
    {
        child0 = litConst0Raw;
    } else if ( Cudd_ReadOne( p->dd ) == nodeE )
    {
        child0 = litConst1Raw;
    }

    int var = nodeVar[i];

    if ( !AddMuxEncodingCudd( p, var, pi, child0, child1 ) )
    {
        printf( "Error adding MUX encoding for node %d\n", i );
        return 0;
    }
    return 1;
}

/**
 * @brief Adds CNF clauses derived from a BDD representation.
 *
 * @details Collects all BDD nodes, allocates SAT variables for them, adds
 *          constant constraints, and encodes the BDD structure into CNF.
 *
 * @param p Pexact struct.
 * @param r BDD root node.
 */
bool ExaManAddCardClausesCudd( PexaMan_t * p, DdNode * r )
{
    if ( r == NULL )
    {
        printf( "Error: BDD root is NULL.\n" );
        return 0;
    }

    // 1.Collect BDD Nodes
    int totalNodes = Cudd_DagSize( r );
    BddCollect_t col;
    col.cap = totalNodes + 2;
    col.nodes = ( DdNode ** )malloc( sizeof( DdNode * ) * col.cap );
    col.index = ( int * )malloc( sizeof( int ) * col.cap );
    col.size = 0;

    for ( int i = 0; i < col.cap; i++ )
    {
        col.index[i] = -1;
    }
    CollectIter( r, &col );

    // 2. SAT-Variable Mapping
    int * nodeVar = ( int * )malloc( sizeof( int ) * col.cap );
    for ( int i = 0; i < col.size; i++ )
    {
        nodeVar[i] = p->iVar++;
    }

    int litConst0Raw = p->iVar++;
    int litConst1Raw = p->iVar++;

    sat_solver_setnvars( p->pSat, p->iVar );

    // Constants variables
    int litConst0 = Abc_Var2Lit( litConst0Raw, 1 );
    int litConst1 = Abc_Var2Lit( litConst1Raw, 0 );
    sat_solver_addclause( p->pSat, &litConst0, &litConst0 + 1 );
    sat_solver_addclause( p->pSat, &litConst1, &litConst1 + 1 );

    // 3. Encoding Loop
    int rootIdx = -1;
    for ( int i = 0; i < col.size; i++ )
    {
        if ( col.nodes[i] == Cudd_Regular( r ) )
        {
            rootIdx = i;
        }
        if ( !ExaManAddCardClausesCuddInner( p, &col, nodeVar, i, litConst0Raw, litConst1Raw ) )
        {
            printf( "Error adding CNF clauses for bdd node %d\n", i );
            free( nodeVar );
            free( ( void * )col.nodes );
            free( ( void * )col.index );
            return 0;
        }
    }
    // 4. Root Constraint: Enforce Root_Var = 1
    if ( rootIdx != -1 )
    {
        int rootLit = Abc_Var2Lit( nodeVar[rootIdx], 0 );
        if ( !sat_solver_addclause( p->pSat, &rootLit, &rootLit + 1 ) )
        {
            printf( "Error adding root constraint for node %d\n", rootIdx );
            free( nodeVar );
            free( ( void * )col.nodes );
            free( ( void * )col.index );
            return 0;
        }
    }

    // Cleanup
    free( nodeVar );
    free( ( void * )col.nodes );
    free( ( void * )col.index );
    return 1;
}


/**
 * @brief Running exact synthesis.
 *
 * @details Running exact synthesis. Calculating a logic network with the least amount of gates.
 *          Iterating over gate count r. For each r, check if a solution exists. First solution
 *          corresponds to a minimum-sized logic network. Adds p variable constraints and cardinality constraints to
 *          identify switching activity optimal solution. Uses BDD type p-variable encoding and polynomial cardinality constraints.
 *
 * @param pPars Input information from executed abc command.
 *
 * @return Returns 0 if synthesis was successful.
 */
int PexaManExactPowerSynthesisBasePower( Bmc_EsPar_t * pPars )
{
    int status = 0;
    abctime clkTotal = Abc_Clock();
    PexaMan_t * p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex( pTruth, pPars->pTtStr );
    if ( ( pPars->nVars < 2 ) || ( pPars->nVars > CONST_FOUR ) )
    {
        printf( "Error: nVars out of valid range (supported: 2..%d).\n", CONST_FOUR );
        return 1;
    }
    p = PexaManAlloc( pPars, pTruth );
    if ( p == NULL )
    {
        printf( "Error: memory allocation failed for PexaMan_t.\n" );
        return 1;
    }
    if ( pTruth[0] & 1 )
    {
        fCompl = 1;
        Abc_TtNot( pTruth, p->nWords );
    }
    CombList_t * list = ( CombList_t * )malloc( sizeof( CombList_t ) );
    if ( list == NULL )
    {
        PexaManFree( p );
        return 1;
    }
    list->len = pow( 2, p->nVars - 1 );
    list->length = 0;
    list->start = NULL;
    int r = 0;
    int act = 0;
    int maxGateCount = MAJ_NOBJS - p->nVars;
    while ( r < maxGateCount )
    {
        if ( act >= CalcMaxAct( r + 1, p->nVars ) )
        {
            r++;
            if ( r >= maxGateCount )
            {
                printf( "No solution found within %d gates.\n", maxGateCount );
                FreeCombList( list );
                free( list );
                PexaManFree( p );
                return 1;
            }
            pPars->nNodes = r + 1;
            if ( !CalculateCombArray( p->nVars, r, list ) )
            {
                printf( "Error: could not calculate combination array.\n" );
                FreeCombList( list );
                free( list );
                PexaManFree( p );
                return 1;
            }
        }
        if ( list->length == 0 || list->start->act != act )
        {
            act++;
            continue;
        }

        {
            Comb_t * node = PopComb( list );
            pPars->nNodes = node->r + 1;
            PexaManFree( p );
            p = PexaManAlloc( pPars, pTruth );
            if ( p == NULL )
            {
                printf( "Error: memory allocation failed for PexaMan_t.\n" );
                free( node->combi );
                free( node );
                FreeCombList( list );
                free( list );
                return 1;
            }
            if ( !ExactPowerSynthesisCNF( pPars, p, node, list ) )
            {
                printf( "Warning: CNF encoding failed for combination act=%d r=%d.\n", node->act, node->r );
                free( node->combi );
                free( node );
                continue;
            }
            status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
            if ( status == 1 )
            {
                free( node->combi );
                free( node );
                PexaManPrintSolution( p, fCompl, true );
                PexaManFree( p );
                Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
                FreeCombList( list );
                free( list );
                return 0;  // Success
            }
            free( node->combi );
            free( node );
            continue;
        }
    }
    FreeCombList( list );
    free( list );
    PexaManFree( p );
    return 1;
}


/**
 * @brief Builds the SAT instance for BDD-based exact power synthesis.
 *
 * @details Adds the base CNF constraints, p-variable BDD encoding, computes the
 *          activity-restricted BDD, and encodes the BDD into CNF.
 *
 * @param pPars Input information from executed abc command.
 * @param p Pexact struct.
 * @param node Combination node describing the current activity/gate candidate.
 *
 * @return Returns status.
 * @retval true if encoding succeeded.
 * @retval false if encoding failed.
 */
bool ExactPowerSynthesisCnfBdd( Bmc_EsPar_t * pPars, PexaMan_t * p, Comb_t * node )
{
    DdManager * dd = Cudd_Init(
        0,  // number of BDD variables initially (0 = dynamic)
        0,  // number of ZDD variables
        CUDD_UNIQUE_SLOTS,
        CUDD_CACHE_SLOTS,
        0  // memory limit (0 = unlimited)
    );
    p->dd = dd;
    if ( !PexaManAddCnfStart( p, pPars->fOnlyAnd ) )
    {
        return 0;
    }

    for ( int iMint = 1; iMint < pow( 2, p->nVars ); iMint++ )
    {
        if ( !PexaManAddCnf( p, iMint ) )
        {
            return 0;
        }
    }
    if ( !PexaManAddPClausesBdd( p ) )
    {
        return 0;
    }
    //
    DdNode * f = CalculateBddCuddSmallerThanMin( dd, p, node->r, node->act, node->act );
    int bddNodes = Cudd_DagSize( f );
    if ( bddNodes == 1 )
    {
        return 0;  // no solution
    }
    // printf("BDD for act=%d r=%d has %d nodes.\n", node->act, node->r, bddNodes);
    if ( !ExaManAddCardClausesCudd( p, f ) )
    {
        printf( "Error adding CNF clauses for BDD with act=%d r=%d.\n", node->act, node->r );
        return 0;
    }
    Cudd_RecursiveDeref( dd, f );
    return 1;
}

/**
 * @brief Builds the SAT instance for BDD-based exact power synthesis with activity range.
 *
 * @details Same as ExactPowerSynthesisCnfBdd but uses an activity interval
 *          defined by delta to relax the BDD selection.
 *
 * @param pPars Input information from executed abc command.
 * @param p Pexact struct.
 * @param node Combination node describing the current activity/gate candidate.
 * @param delta Activity range offset.
 *
 * @return Returns status.
 * @retval true if encoding succeeded.
 * @retval false if encoding failed.
 */
bool ExactPowerSynthesisCnfBddRange( Bmc_EsPar_t * pPars, PexaMan_t * p, Comb_t * node, int delta )
{
    DdManager * dd = Cudd_Init(
        0,  // number of BDD variables initially (0 = dynamic)
        0,  // number of ZDD variables
        CUDD_UNIQUE_SLOTS,
        CUDD_CACHE_SLOTS,
        0  // memory limit (0 = unlimited)
    );
    p->dd = dd;
    if ( !PexaManAddCnfStart( p, pPars->fOnlyAnd ) )
    {
        return 0;
    }

    for ( int iMint = 1; iMint < pow( 2, p->nVars ); iMint++ )
    {
        if ( !PexaManAddCnf( p, iMint ) )
        {
            return 0;
        }
    }
    if ( !PexaManAddPClausesBdd( p ) )
    {
        return 0;
    }
    //
    DdNode * f = CalculateBddCuddSmallerThanMin( dd, p, node->r, node->act + delta, node->act );
    int bddNodes = Cudd_DagSize( f );
    if ( bddNodes == 1 )
    {
        return 0;  // no solution
    }
    if ( !ExaManAddCardClausesCudd( p, f ) )
    {
        printf( "Error adding CNF clauses for BDD with act=%d r=%d.\n", node->act, node->r );
        return 0;
    }
    Cudd_RecursiveDeref( dd, f );
    return 1;
}

/**
 * @brief Running exact synthesis with BDD-based biary search over activity.
 *
 * @details Uses a stepwise activity search and BDD-based CNF encoding to find an
 *          optimal solution with fewer solver iterations.
 *
 * @param pPars Input information from executed abc command.
 * @param stepSize Initial activity step size.
 *
 * @return Returns 0 if synthesis was successful.
 * @retval 1 if synthesis failed or no solution was found.
 */
int PexaManExactPowerSynthesisBasePowerBDD( Bmc_EsPar_t * pPars )
{
    int status = 0;
    abctime clkTotal = Abc_Clock();
    PexaMan_t * p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex( pTruth, pPars->pTtStr );
    if ( ( pPars->nVars < 2 ) || ( pPars->nVars > CONST_FOUR ) )
    {
        printf( "Error: nVars out of valid range (supported: 2..%d).\n", CONST_FOUR );
        return 1;
    }
    p = PexaManAlloc( pPars, pTruth );
    if ( p == NULL )
    {
        printf( "Error: memory allocation failed for PexaMan_t.\n" );
        return 1;
    }
    if ( pTruth[0] & 1 )
    {
        fCompl = 1;
        Abc_TtNot( pTruth, p->nWords );
    }
    int r = 0;
    int act = 0;
    int maxGateCount = MAJ_NOBJS - p->nVars;

    while ( r < maxGateCount )
    {
        if ( act >= CalcMaxAct( r + 1, p->nVars ) )
        {
            r++;
            if ( r >= maxGateCount )
            {
                printf( "No solution found within %d gates.\n", maxGateCount );
                PexaManFree( p );
                return 1;
            }
            pPars->nNodes = r + 1;
        }
        {
            for ( int rIt = 1; rIt < r + 1; rIt++ )
            {
                // printf( "Trying combination act=%d r=%d.\n", act, rIt );
                Comb_t node;
                node.act = act;
                node.r = rIt;
                pPars->nNodes = rIt + 1;
                PexaManFree( p );
                p = PexaManAlloc( pPars, pTruth );
                if ( p == NULL )
                {
                    printf( "Error: memory allocation failed for PexaMan_t.\n" );
                    return 1;
                }
                if ( !ExactPowerSynthesisCnfBdd( pPars, p, &node ) )
                {
                    continue;
                }

                status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
                if ( status == 1 )
                {
                    PexaManPrintSolution( p, fCompl, true );
                    PexaManFree( p );
                    Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
                    return 0;  // Success
                }
            }
        }
        act++;
    }
    PexaManFree( p );
    return 1;
}

/**
 * @brief Inner loop for BDD-based biary activity search.
 *
 * @details Tries all gate counts for the given activity target, rebuilds the
 *          SAT instance for each attempt, and updates the activity delta after
 *          successful solving.
 *
 * @param pPars Input information from executed abc command.
 * @param p Pointer to Pexact struct pointer.
 * @param pTruth Original truth table.
 * @param r Current gate count.
 * @param act Pointer to current activity value.
 * @param delta Pointer to current activity step size.
 *
 * @return Returns status.
 * @retval 0 if a solution was found.
 * @retval 1 if no solution was found.
 */
int PexaManExactPowerSynthesisBasePowerBDDBiaryInner( Bmc_EsPar_t * pPars, PexaMan_t ** p, word * pTruth, const int r, const int * act, int * delta )
{
    for ( int rIt = 1; rIt < r + 1; rIt++ )
    {
        Comb_t node;
        node.act = *act;
        node.r = rIt;
        pPars->nNodes = rIt + 1;
        PexaManFree( *p );
        *p = PexaManAlloc( pPars, pTruth );
        if ( p == NULL )
        {
            printf( "Error: memory allocation failed for PexaMan_t.\n" );
            return 1;
        }
        if ( !ExactPowerSynthesisCnfBddRange( pPars, *p, &node, *delta ) )
        {
            continue;
        }
        int status = sat_solver_solve( ( *p )->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == 1 )
        {
            int actSolution = PexaManGetAct( *p );
            *delta = ( actSolution - *act ) / 2;
            printf( "Found solution for act=%d delta=%d\n", PexaManGetAct( *p ), *delta );
            if ( *delta > 0 )
            {
                rIt = 0;
                continue;
            }
            return 0;  // Success
        }
    }
    return 1;
}

/**
 * @brief Running exact synthesis with BDD-based biary search over activity.
 *
 * @details Repeats BDD-based solving while adapting the activity window until
 *          a feasible solution is found or the gate limit is reached.
 *
 * @param pPars Input information from executed abc command.
 * @param stepSize Initial activity step size.
 *
 * @return Returns 0 if synthesis was successful.
 * @retval 1 if synthesis failed or no solution was found.
 */
int PexaManExactPowerSynthesisBasePowerBDDBiary( Bmc_EsPar_t * pPars, int stepSize )
{
    abctime clkTotal = Abc_Clock();
    PexaMan_t * p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex( pTruth, pPars->pTtStr );
    int delta = stepSize;
    if ( ( pPars->nVars < 2 ) || ( pPars->nVars > CONST_FOUR ) )
    {
        printf( "Error: nVars out of valid range (supported: 2..%d).\n", CONST_FOUR );
        return 1;
    }
    p = PexaManAlloc( pPars, pTruth );
    if ( p == NULL )
    {
        printf( "Error: memory allocation failed for PexaMan_t.\n" );
        return 1;
    }
    if ( pTruth[0] & 1 )
    {
        fCompl = 1;
        Abc_TtNot( pTruth, p->nWords );
    }
    int r = 0;
    int act = 0;
    int maxGateCount = MAJ_NOBJS - p->nVars;

    while ( r < maxGateCount )
    {
        while ( act + delta >= CalcMaxAct( r + 1, p->nVars ) )
        {
            r++;
            if ( r >= maxGateCount )
            {
                printf( "No solution found within %d gates.\n", maxGateCount );
                PexaManFree( p );
                return 1;
            }
            pPars->nNodes = r + 1;
        }
        int status = PexaManExactPowerSynthesisBasePowerBDDBiaryInner( pPars, &p, pTruth, r, &act, &delta );
        if ( status == 0 )
        {
            PexaManPrintSolution( p, fCompl, true );
            PexaManFree( p );
            Abc_PrintTime( 1, "Total runtime", Abc_Clock() - clkTotal );
            return 0;
        }
        act += delta;
    }
    PexaManFree( p );
    return 1;
}
