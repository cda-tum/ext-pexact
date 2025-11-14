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

#include <iostream>

namespace
{

// Very simple ABC command: prints a greeting and its command line argumentss
int Pexact_Command( Abc_Frame_t * pAbc, int argc, char ** argv )
{
    std::cout << "Hello world!" << std::endl;

    for ( int i = 0; i < argc; i++ )
    {
        std::cout << "  argv[" << i << "]: " << argv[i] << std::endl;
    }

    return 0;
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
