/*
 * This file is part of Freecell Solver. It is subject to the license terms in
 * the COPYING.txt file found in the top-level directory of this distribution
 * and at http://fc-solve.shlomifish.org/docs/distro/COPYING.html . No part of
 * Freecell Solver, including this file, may be copied, modified, propagated,
 * or distributed except according to the terms contained in the COPYING file.
 *
 * Copyright (c) 2000 Shlomi Fish
 */
/*
 * gen_ms_boards__rand.h - a header file that defines some
 * static (and preferably inline) routines for the MS Freecell deals
 * generation random number generator.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "rinutils.h"

typedef u_int32_t microsoft_rand_uint_t;

typedef long long microsoft_rand_t;

static GCC_INLINE microsoft_rand_uint_t microsoft_rand_rand(
    microsoft_rand_t *const my_rand)
{
    *my_rand = ((*my_rand) * 214013 + 2531011);
    return ((*my_rand) >> 16) & 0x7fff;
}

static GCC_INLINE microsoft_rand_uint_t microsoft_rand_randp(
    microsoft_rand_t *const my_rand)
{
    *my_rand = ((*my_rand) * 214013 + 2531011);
    return ((*my_rand) >> 16) & 0xffff;
}

static GCC_INLINE microsoft_rand_uint_t microsoft_rand__game_num_rand(
    microsoft_rand_t *const seedx_ptr, const long long gnGameNumber)
{
    if (gnGameNumber < 0x100000000LL)
    {
        const microsoft_rand_uint_t ret = microsoft_rand_rand(seedx_ptr);
        return ((gnGameNumber < 0x80000000) ? ret : (ret | 0x8000));
    }
    else
    {
        return microsoft_rand_randp(seedx_ptr) + 1;
    }
}

#ifdef __cplusplus
}
#endif
