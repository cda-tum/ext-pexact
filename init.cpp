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

extern "C"
{
#include "pexact.h"
}

#include "stdio.h"

namespace
{
const int DECIMAL_BASE = 10;

/**
 * @brief Pexact command.
 *
 * @details Extracts command input information, initializes Bmc_EsPar_t struct and finally executes
 *          the exact synthesis command from pexact.c.
 *
 * @param pAbc Abc frame.
 * @param argc Arg count.
 * @param argv Arg array
 */
int PexactCommand( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    int c;
    char * pEnd;
    Bmc_EsPar_t pars;
    Bmc_EsPar_t * pPars = &pars;
    Bmc_EsParSetDefault( pPars );
    Extra_UtilGetoptReset();
    Abc_FrameInit( pAbc );
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
            pPars->nVars = strtol( argv[globalUtilOptind], &pEnd, DECIMAL_BASE );
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
    return PexaManExactPowerSynthesisBasePower( pPars, 2 );
usage:
    Abc_Print( -2, "usage: pexact [-I] <hex>\n" );
    Abc_Print( -2, "\t           exact synthesis of multi-input function using two-input gates\n" );
    Abc_Print( -2, "\t-I <num> : the number of input variables [default = %d]\n", pPars->nVars );
    return 1;
}
/**
 * @brief Abc startup initialization.
 *
 * @details Called during ABC startup.
 *
 * @param pAbc Abc frame.
 */
void Init( Abc_Frame_t * pAbc )
{
    Cmd_CommandAdd( pAbc, "pexact", "pexact", PexactCommand, 0 );
}
/**
 * @brief Destructor.
 *
 * @param pAbc Abc frame.
 */
void Destroy( Abc_Frame_t * pAbc )
{
}
Abc_FrameInitializer_t s_frameInitializer = { Init, Destroy };
/**
 * @brief Register struct.
 *
 * @details register the initializer a constructor of a global object
 *          called before main (and ABC startup)
 */
struct Register_t_ {
    Register_t_()
    {
        Abc_FrameAddInitializer( &s_frameInitializer );
    }
} s_pexactRegister;

}  // unnamed namespace
