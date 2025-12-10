/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

#include "pexact.hpp"

#include "misc/extra/extra.h"
#include "misc/util/utilTruth.h"
#include "sat/bmc/bmc.h"
#include "sat/bsat/satStore.h"
#include "sat/cnf/cnf.h"

#include <math.h>
#include <stdio.h>
/*
 * @brief Evaluates truth table pointers.
 *
 * @details Returns pointer to the v'th input truth table using Vec_WrdEntryP.
 *
 * @param p: pexact struct.
 * @param v: v'th input of the network.
 *
 * @return Word pointer.
 *
 */
static inline word * PexaManTruth( PexaMan_t * p, int v ) { return Vec_WrdEntryP( p->vInfo, p->nWords * v ); }
/*
 * @brief Initialization of truth table variables.
 *
 * @details Initializes p->vInfo and sets Abc_TtIthVar.
 *
 * @param p: Pexact struct.
 *
 * @return Vec_Wrd_t pointer to p->vInfo.
 *
 */
static Vec_Wrd_t * PexaManTruthTables( PexaMan_t * p )
{
    p->vInfo = Vec_WrdStart( p->nWords * ( p->nObjs + 1 ) );
    int i;
    for ( i = 0; i < p->nVars; i++ )
    {
        Abc_TtIthVar( PexaManTruth( p, i ), i, p->nVars );
    }
    //Dau_DsdPrintFromTruth( PexaManTruth(p, p->nObjs), p->nVars );
    return p->vInfo;
}
/*
 * @brief Initialization od variables for CNF encoding.
 *
 * @details Initializes all required variables for CNF including variables for: truth-tables, connectivity, functinallity of gates.
 *
 * @param p: Pexact struct.
 *
 * @return int as next available free variable.
 *
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
    //printf( "The number of parameter variables = %d.\n", p->iVar );
    return p->iVar;
    // printout
    for ( i = p->nVars; i < p->nObjs; i++ )
    {
        printf( "Node %d\n", i );
        for ( j = 0; j < p->nObjs; j++ )
        {
            for ( k = 0; k < 2; k++ )
            {
                printf( "%3d ", p->VarMarks[i][k][j] );
            }
            printf( "\n" );
        }
    }
    return p->iVar;
}
/*
 * @brief Allocation pexact struct.
 *
 * @details Allocates all required variables for pexact.
 *
 * @param pPars: Terminal input parameters struct from 'pexact -...' command.
 * @param pTruth: Truth table word pointer.
 *
 * @return PexaMan_t pointer as allocated pexact struct.
 *
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
    p->i_p = 0;
    p->o_l = 0;
    p->i_o = 0;
    p->i_xo = 0;
    p->i_mintermvars = 0;
    p->vOutList = Vec_WecStart( p->nObjs );
    p->iVar = PexaManMarkup( p );
    p->vInfo = PexaManTruthTables( p );
    p->pSat = sat_solver_new();
    sat_solver_setnvars( p->pSat, p->iVar );
    return p;
}
/*
 * @brief Deallocation pexact struct.
 *
 * @details Deallocates all previous allocated memory for pexact struct.
 *
 * @param p: Pexact struct.
 */
static void PexaManFree( PexaMan_t * p )
{
    sat_solver_delete( p->pSat );
    Vec_WrdFree( p->vInfo );
    Vec_WecFree( p->vOutList );
    ABC_FREE( p );
}
/*
 * @brief Fanin evaluation.
 *
 * @details Determines based on a solution from SAT solver, which fanin a gate has. Return variable indicating the k'th input of gate i
 *
 * @param p: Pexact struct.
 * @param i: gate i.
 * @param k: input k of gate i.
 *
 * @return  variable of input (either fanin or other gate).
 */
static inline int PexaManFindFanin( PexaMan_t * p, int i, int k )
{
    int j;
    int count = 0;
    int iVar = -1;
    for ( j = 0; j < p->nObjs; j++ )
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
/*
 * @brief Evaluation of turth table.
 *
 * @details Determines based on a solution from SAT solver, if the resulting truth-table matches with the specified one. Needed for CEGAR optimizattion approach.
 *          Returns first mismatching minterm.
 *
 * @param p: Pexact struct.
 *
 * @return  Index of first mismatching minterm.
 */
static inline int PexaManEval( PexaMan_t * p )
{
    const int flag = 0;
    int i;
    int k;
    int iMint;
    word * pFanins[2];
    for ( i = p->nVars; i < p->nObjs; i++ )
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
            Abc_TtAndCompl( PexaManTruth( p, p->nObjs ), pFanins[0], static_cast<int>( ( k & 1 ) == 0 ), pFanins[1], static_cast<int>( ( k >> 1 ) == 0 ), p->nWords );
            Abc_TtOr( PexaManTruth( p, i ), PexaManTruth( p, i ), PexaManTruth( p, p->nObjs ), p->nWords );
        }
    }
    if ( flag && p->nVars >= CONST_SIX )
    {
        iMint = Abc_TtFindLastDiffBit( PexaManTruth( p, p->nObjs - 1 ), p->pTruth, p->nVars );
    } else
    {
        iMint = Abc_TtFindFirstDiffBit( PexaManTruth( p, p->nObjs - 1 ), p->pTruth, p->nVars );
    }
    //flag ^= 1;
    assert( iMint < ( 1 << p->nVars ) );
    return iMint;
}
/*
 * @brief Evaluation n'th bit in value for binary representation.
 *
 * @details Determines value of n'th bit of integer value, assuming a binary representation.
 *
 * @param value: Binary Integer.
 * @param n: n'th bit.
 *
 * @return  Returns either 0 or 1.
 */
const int ValueNthBit( int value, int n )
{
    return ( value >> n ) & 1;
}
/*
 * @brief Evaluates resulting switching activity.
 *
 * @details Extracting information from solution and calculating overall switching activity of network.
 *
 * @param p: Pexact struct.
 *
 * @return  Returns switching activity.
 */
static int PexaManGetAct( PexaMan_t * p )
{
    const int mulPot = ( pow( 2, p->nVars ) );
    const int len = ( p->nObjs ) * mulPot;
    int xIt[len];
    const int xiBase = ( p->nNodes * ( 2 * p->nVars + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );
    for ( int i = p->nVars; i < p->nVars + p->nNodes - 1; i++ )
    {
        const int index = i * mulPot;
        xIt[index] = 0;
        for ( int t = 1; t < pow( 2, p->nVars ); t++ )
        {
            const int index = ( i * mulPot ) + t;
            xIt[index] = sat_solver_var_value( p->pSat, xiBase + ( CONST_THREE * ( i - p->nVars + 1 ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) ) );
        }
    }
    int sumAct = 0;
    for ( int i = p->nVars; i < p->nObjs - 1; i++ )
    {
        int sum0 = 0;
        int sum1 = 0;
        int minSum = 0;
        for ( int t = 0; t < pow( 2, p->nVars ); t++ )
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
        sumAct += 2 * minSum * ( pow( 2, p->nVars ) - minSum );
    }
    return sumAct;
}
/*
 * @brief Printing solution of SAT solver.
 *
 * @details Extracting information from solution and printing connectivity and truth tables.
 *
 * @param p: Pexact struct.
 * @param fCompl: Parameter indicating if least gate is complemented or not.
 *
 */
static void PexaManPrintSolution( PexaMan_t * p, int fCompl )
{
    int i;
    int k;
    int iVar;
    printf( "Realization of given %d-input function using %d two-input gates complementary=%d:\n", p->nVars, p->nNodes, fCompl );
    //    for ( i = p->nVars + 2; i < p->nObjs; i++ )
    for ( i = p->nObjs - 1; i >= p->nVars; i-- )
    {
        const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
        const int val1 = sat_solver_var_value( p->pSat, iVarStart );
        const int val2 = sat_solver_var_value( p->pSat, iVarStart + 1 );
        const int val3 = sat_solver_var_value( p->pSat, iVarStart + 2 );
        if ( i == p->nObjs - 1 && fCompl )
        {
            printf( "%02d = 4\'b%d%d%d1(", i, static_cast<int>( val3 == 0 ), static_cast<int>( val2 == 0 ), static_cast<int>( val1 == 0 ) );
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
    printf( "Printing overall Truth Table...\n" );
    const int len = ( p->nObjs ) * ( pow( 2, p->nVars ) );
    int xIt[len];
    const int xiBase = ( p->nNodes * ( ( 2 * p->nVars ) + p->nNodes - 1 ) ) - p->nNodes + ( CONST_THREE * p->nNodes );

    for ( int i = 0; i < p->nVars; i++ )
    {
        for ( int t = 0; t < pow( 2, p->nVars ); t++ )
        {
            const int index = ( i * ( pow( 2, p->nVars ) ) ) + t;
            xIt[index] = ValueNthBit( t, i );
        }
    }

    for ( int i = p->nVars; i < p->nVars + p->nNodes - 1; i++ )
    {
        const int index = i * ( pow( 2, p->nVars ) );
        xIt[index] = 0;
        for ( int t = 1; t < pow( 2, p->nVars ); t++ )
        {
            const int index = ( i * ( pow( 2, p->nVars ) ) ) + t;
            xIt[index] = sat_solver_var_value( p->pSat, xiBase + ( CONST_THREE * ( i - p->nVars + 1 ) ) + ( ( t - 1 ) * ( CONST_THREE * p->nNodes ) ) );
        }
    }
    for ( int i = 0; i < p->nObjs - 1; i++ )
    {
        printf( "i=%d:", i );
        for ( int t = 0; t < pow( 2, p->nVars ); t++ )
        {
            const int index = ( i * ( pow( 2, p->nVars ) ) ) + t;
            printf( "%d", xIt[index] );
        }
        printf( "\n" );
    }
    const int iVarStart = 1 + ( CONST_THREE * ( p->nObjs - 1 - p->nVars ) );
    int fOut[CONST_FOUR];
    fOut[CONST_ZERO] = fCompl;
    fOut[CONST_ONE] = fCompl ? static_cast<bool>( sat_solver_var_value( p->pSat, iVarStart ) == 0 ) : sat_solver_var_value( p->pSat, iVarStart );
    fOut[CONST_TWO] = fCompl ? static_cast<bool>( sat_solver_var_value( p->pSat, iVarStart + 1 ) == 0 ) : sat_solver_var_value( p->pSat, iVarStart + 1 );
    fOut[CONST_THREE] = fCompl ? static_cast<bool>( sat_solver_var_value( p->pSat, iVarStart + 2 ) == 0 ) : sat_solver_var_value( p->pSat, iVarStart + 2 );
    const int i0 = PexaManFindFanin( p, p->nObjs - 1, 0 );
    const int i1 = PexaManFindFanin( p, p->nObjs - 1, 1 );
    printf( "i=%d:", p->nObjs - 1 );
    for ( int t = 0; t < pow( 2, p->nVars ); t++ )
    {
        const int index0 = ( i0 * ( pow( 2, p->nVars ) ) ) + t;
        const int index1 = ( i1 * ( pow( 2, p->nVars ) ) ) + t;
        const int index = ( xIt[index1] << 1 ) + ( xIt[index0] );
        printf( "%d", fOut[index] );
    }
    printf( "\n" );
    printf( "\n" );
    const int sumAct = PexaManGetAct( p );
    printf( "Switching Activity=%d\n", sumAct );
    printf( "Number of Gates: r=%d\n", p->nNodes );
}
/*
 * @brief Adding Input Uniqueness CNF encoding.
 *
 * @details Adding constraints to encoding that ensure that not two gates exist that use the same two inputs.
 *
 * @param p: Pexact struct.
 * @param nList: Iteration.
 * @param pList: List variables.
 * @param pList2: List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfInpUniq( PexaMan_t * p, int nList, int pList[MAJ_NOBJS], int pList2[2] )
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
/*
 * @brief Adding symmetry breaking constrains helper.
 *
 * @details Adding constraints to encoding that reduces overall search space. Inner helper function of AddCnfSymBreaking.
 *
 * @param p: Pexact struct.
 * @param i: Gate iteration variable.
 * @param j: Iteration variable over all objects(nVars inputs + nNodes internal nodes).
 * @param k: Gate input iteration variable.
 * @param pList2: List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfSymBreakingInner( PexaMan_t * p, int i, int j, int k, int pList2[2] )
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
/*
 * @brief Adding symmetry breaking constrains.
 *
 * @details Adding constraints to encoding that reduces overall search space.
 *
 * @param p: Pexact struct.
 * @param i: Gate iteration variable.
 * @param k: Gate input iteration variable.
 * @param pList2: List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfSymBreaking( PexaMan_t * p, int i, int k, int pList2[2] )
{
    // symmetry breaking
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
/*
 * @brief Adding gate functionality constraints.
 *
 * @details Adding constraints to encoding that ensure that gates only behave as nontrivial operators.
 *
 * @param p: Pexact struct.
 * @param fOnlyAnd: Least gate is inverted.
 * @param i: Gate iteration variable.
 * @param k: Gate input iteration variable.
 * @param pList: List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfTwoInputFunc( PexaMan_t * p, int fOnlyAnd, int i, int k, int pList[MAJ_NOBJS] )
{
    const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
    // two input functions
    for ( k = 0; k < CONST_THREE; k++ )
    {
        pList[0] = Abc_Var2Lit( iVarStart, static_cast<int>( k == 1 ) );
        pList[1] = Abc_Var2Lit( iVarStart + 1, static_cast<int>( k == 2 ) );
        pList[2] = Abc_Var2Lit( iVarStart + 2, static_cast<int>( k != 0 ) );
        if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
        {
            return 0;
        }
    }
    if ( fOnlyAnd )
    {
        pList[0] = static_cast<int>( Abc_Var2Lit( iVarStart, 1 ) );
        pList[1] = static_cast<int>( Abc_Var2Lit( iVarStart + 1, 1 ) );
        pList[2] = static_cast<int>( Abc_Var2Lit( iVarStart + 2, 0 ) );
        if ( !sat_solver_addclause( p->pSat, pList, pList + CONST_THREE ) )
        {
            return 0;
        }
    }
    return 1;
}
/*
 * @brief Constrining that every output should be used.
 *
 * @details Adding constraints to encoding that ensure that each output shall be used.
 *
 * @param p: Pexact struct.
 * @param i: Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfStartOutUsed( PexaMan_t * p, int i )
{
    // outputs should be used
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
/*
 * @brief Inner helper function of PexaManAddCnfStart.
 *
 * @details Inner helper function of PexaManAddCnfStart. Adding all used constraints for each gate i.
 *
 * @param p: Pexact struct.
 * @param fOnlyAnd: Least gate is inverted.
 * @param i: Gate iteration variable.
 * @param pList: List variables.
 * @param pList2: List variables.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfStartInner( PexaMan_t * p, int i, int pList[MAJ_NOBJS], int pList2[2], int fOnlyAnd )
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

        if ( AddCnfTwoInputFunc( p, fOnlyAnd, i, k, pList ) == 0 )
        {
            return 0;
        }
    }
    return 1;
}
/*
 * @brief Adding basic constraints for pexact synthesis.
 *
 * @details Iterating over all gates and applying AddCnfStartInner to add all basic constraints.
 *
 * @param p: Pexact struct.
 * @param fOnlyAnd: Least gate is inverted.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int PexaManAddCnfStart( PexaMan_t * p, int fOnlyAnd )
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
    if ( AddCnfStartOutUsed( p, i ) == 0 )
    {
        return 0;
    }

    return 1;
}
/*
 * @brief Inner function adding fanin connectivity constraints.
 *
 * @details Inner function of AddCnfFaninCon. Constraining which output value a gate i has for which values of input.
 *
 * @param p: Pexact struct.
 * @param i Gate iteration variable.
 * @param k Truth table iteration variable 0,...,3.
 * @param j All Objects(inputs+gates) iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfFaninConInner( PexaMan_t * p, int i, int k, int j )
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
            pList[nList++] = Abc_Var2Lit( iBaseSatVarJ + 2, static_cast<int>( n == 0 ) );
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
/*
 * @brief Adding fanin connectivity constraints.
 *
 * @details Constraining which output value a gate i has for which values of input.
 *
 * @param p: Pexact struct.
 * @param i Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfFaninCon( PexaMan_t * p, int i )
{
    // fanin connectivity
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
/*
 * @brief Adding fanin Node functionality constraints.
 *
 * @details Constraining which output value a gate i has depending on the functionality variables(AND,OR,XOR).
 *
 * @param p: Pexact struct.
 * @param iMint: Minterm iteration variable.
 * @param i Gate iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int AddCnfNodeFunc( PexaMan_t * p, int iMint, int i )
{
    int k = 0;
    int n = 0;
    const int value = Abc_TtGetBit( p->pTruth, iMint );
    const int iVarStart = 1 + ( CONST_THREE * ( i - p->nVars ) );
    const int iBaseSatVarI = p->iVar + ( CONST_THREE * ( i - p->nVars ) );
    for ( n = 0; n < 2; n++ )
    {
        if ( i == p->nObjs - 1 && n == value )
        {
            continue;
        }
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
                pList[nList++] = Abc_Var2Lit( iBaseSatVarI + 2, static_cast<int>( n == 0 ) );
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
    }
    return 1;
}
/*
 * @brief Adding hole functionality constraintys for minterm iMint.
 *
 * @details Constraining functionality of logic network for a given minterm iMing.
 *          Including fanin connectivity and gate functionality.
 *
 * @param p: Pexact struct.
 * @param iMint: Minterm iteration variable.
 *
 * @return  Returns 0 if error during encoding occurs.
 */
static int PexaManAddCnf( PexaMan_t * p, int iMint )
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
/*
 * @brief Running exact synthesis.
 *
 * @details Running exact synethesis. Calculating logic network with least amount of gates.
 *          Iterating over gate count r. For each r checking if a solution exists. First solution
 *          corresponds to minimum sized logic network.
 *
 * @param pPars: Input information from executed abc command.
 *
 */
void PowerExactSynthesisBase( Bmc_EsPar_t * pPars )
{
    int status;
    int iMint = 1;
    PexaMan_t * p;
    int fCompl = 0;
    word pTruth[16];
    Abc_TtReadHex( pTruth, pPars->pTtStr );
    assert( pPars->nVars <= CONST_TEN );
    p = PexaManAlloc( pPars, pTruth );
    if ( pTruth[0] & 1 )
    {
        fCompl = 1;
        Abc_TtNot( pTruth, p->nWords );
    }
    int r = 0;
    const int maxNodes = 100;
    while ( r < maxNodes )
    {
        PexaManFree( p );
        pPars->nNodes = r + 1;
        p = PexaManAlloc( pPars, pTruth );
        status = PexaManAddCnfStart( p, pPars->fOnlyAnd );
        assert( status );
        for ( iMint = 1; iMint < pow( 2, p->nVars ); iMint++ )
        {
            if ( !PexaManAddCnf( p, iMint ) )
            {
                printf( "The problem has no solution.\n" );
                break;
            }
        }
        status = sat_solver_solve( p->pSat, NULL, NULL, 0, 0, 0, 0 );
        if ( status == 1 )
        {
            PexaManPrintSolution( p, fCompl );
            PexaManFree( p );
            break;
        }
        r++;
    }
    if ( r >= maxNodes )
    {
        printf( "No solution found within %d gates.\n", maxNodes );
        PexaManFree( p );
    }
}
