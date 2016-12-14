/*
 * This file is part of Freecell Solver. It is subject to the license terms in
 * the COPYING.txt file found in the top-level directory of this distribution
 * and at http://fc-solve.shlomifish.org/docs/distro/COPYING.html . No part of
 * Freecell Solver, including this file, may be copied, modified, propagated,
 * or distributed except according to the terms contained in the COPYING file.
 *
 * Copyright (c) 2012 Shlomi Fish
 */
/*
 * generic_tree.h - provide a unified interface to either kaz_tree.h
 * or libavl/rb.h .
 */

#pragma once

#include "config.h"

#ifdef FCS_DBM_USE_LIBAVL

#include "rb.h"

typedef struct rb_table dict_t;
typedef void *dict_key_t;
#define fc_solve_kaz_tree_destroy(tree) rb_destroy(tree, NULL)
#define fc_solve_kaz_tree_create(comparator, context, meta, recycle_bin_ptr)   \
    rb_create(comparator, context, meta, recycle_bin_ptr)
#define fc_solve_kaz_tree_lookup_value(tree, value) rb_find(tree, value)
#define fc_solve_kaz_tree_delete_by_value(tree, value) rb_delete(tree, value)
#define fc_solve_kaz_tree_alloc_insert(tree, value) rb_insert(tree, value)
#define dict_allocator rb_allocator
#else

#include "rinutils.h"
#include "kaz_tree.h"

static GCC_INLINE void fc_solve_kaz_tree_delete_by_value(
    dict_t *kaz_tree, dict_key_t value)
{
    fc_solve_kaz_tree_delete_free(
        kaz_tree, fc_solve_kaz_tree_lookup(kaz_tree, value));
}

#endif
