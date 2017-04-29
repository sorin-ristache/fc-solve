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
 * gen_ms_boards__hll_iface.h - high-level-language interface to the rand.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "gen_ms_boards__rand.h"

typedef struct
{
    microsoft_rand_t gamenumber;
    microsoft_rand_t seedx;
} fc_solve__hll_ms_rand_t;

extern fc_solve__hll_ms_rand_t *fc_solve__hll_ms_rand__get_singleton(void);
extern void fc_solve__hll_ms_rand__init(
    fc_solve__hll_ms_rand_t *const instance, const char *const gamenumber);
extern int fc_solve__hll_ms_rand__mod_rand(
    fc_solve__hll_ms_rand_t *const instance, const int limit);

#ifdef __cplusplus
}
#endif