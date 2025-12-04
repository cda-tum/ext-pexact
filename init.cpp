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
int PexactCommand( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    Bmc_EsPar_t pars;
    Bmc_EsPar_t * pPars = &pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    while ( ( c = Extra_UtilGetopt( argc, argv, "I" ) ) != EOF )
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
            break;
        default:
            goto usage;
        }
    }
    if ( argc == globalUtilOptind + 1 )
    {
        if ( strstr( argv[globalUtilOptind], "." ) )
        {
            return 0;
        }
        pPars->pTtStr = argv[globalUtilOptind];
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
    if ( ( pPars->nVars ) > 4 )
    {
        Abc_Print( -1, "Function should not have more than 4 inputs.\n" );
        return 1;
    }
    std::cout << "Number of Inputs:" << pPars->nVars << "\n";
    return 1;
usage:
    Abc_Print( -2, "usage: twoexact [-I] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of multi-input function using two-input gates\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", pPars->nVars );
    return 1;
}

// called during ABC startup
void Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "pexact", "pexact", PexactCommand, 0 );
}

// called during ABC termination
void Destroy( Abc_Frame_t * pAbc )
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frameInitializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct register_t_ {
    register_t_()
    {
        Abc_FrameAddInitializer( &frameInitializer );
    }
} pexactRegister;

}  // unnamed namespace
