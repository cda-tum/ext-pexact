/*
 * Copyright (c) 2025 Chair for Design Automation, TUM
 * All rights reserved.
 *
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License
 */

#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bmc/bmc.h"

#include <iostream>

namespace
{

// Very simple ABC command: prints a greeting and its command line argumentss
int Pexact_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Bmc_EsPar_t Pars, *pPars = &Pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "IN" ) ) != EOF )
    {
        switch ( c )
        {
        case 'I':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-I\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nVars = atoi( argv[globalUtilOptind] );
            globalUtilOptind++;
            if ( pPars->nVars < 0 )
                goto usage;
            break;
        case 'N':
            if ( globalUtilOptind >= argc )
            {
                Abc_Print( -1, "Command line switch \"-N\" should be followed by an integer.\n" );
                goto usage;
            }
            pPars->nNodes = atoi( argv[globalUtilOptind] );
            globalUtilOptind++;
            if ( pPars->nNodes < 0 )
                goto usage;
            break;
        case 'h':
            goto usage;
        default:
            goto usage;
        }
    }
    if ( pPars->pTtStr == NULL )
    {
        Abc_Print( -1, "Truth table should be given on the command line.\n" );
        return 1;
    }
    if ( pPars->nVars >= 2 && ( 1 << ( pPars->nVars - 2 ) ) != ( int )strlen( pPars->pTtStr ) )
    {
        Abc_Print( -1, "Truth table is expected to have %d hex digits (instead of %d).\n", ( 1 << ( pPars->nVars - 2 ) ), strlen( pPars->pTtStr ) );
        return 1;
    }
    if ( pPars->nVars > pPars->nNodes * ( 2 - 1 ) + 1 )
    {
        Abc_Print( -1, "Function with %d variables cannot be implemented with %d two-input gates.\n", pPars->nVars, pPars->nNodes );
        return 1;
    }
    if ( pPars->nVars > 4 )
    {
        Abc_Print( -1, "Function should not have more than 4 inputs.\n" );
        return 1;
    }


usage:
    Abc_Print( -2, "usage: twoexact [-IN] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of multi-input function using two-input gates\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", pPars->nVars );
    Abc_Print( -2, "\t-N <num> : the number of two-input nodes [default = %d]\n", pPars->nNodes );
    return 1;
}

// called during ABC startup
void init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "pexact", "pexact", Pexact_Command, 0 );
}

// called during ABC termination
void destroy( Abc_Frame_t * pAbc )
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar {
    registrar()
    {
        Abc_FrameAddInitializer( &frame_initializer );
    }
} pexact_registrar;

}  // unnamed namespace
