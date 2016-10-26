/*
 * This file is part of Freecell Solver. It is subject to the license terms in
 * the COPYING.txt file found in the top-level directory of this distribution
 * and at http://fc-solve.shlomifish.org/docs/distro/COPYING.html . No part of
 * Freecell Solver, including this file, may be copied, modified, propagated,
 * or distributed except according to the terms contained in the COPYING file.
 *
 * Copyright (c) 2009 Shlomi Fish
 */
/*
 * simpsim.h - header file of the Simple Simon move functions
 * ("solve-for-state"/"sfs").
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "config.h"
/* For fcs_state_keyval_pair_t */
#include "state.h"
/* For fc_solve_soft_thread_t and fcs_derived_states_list_t */
#include "instance.h"

#ifndef FCS_DISABLE_SIMPLE_SIMON

DECLARE_MOVE_FUNCTION(fc_solve_sfs_simple_simon_move_sequence_to_founds);

DECLARE_MOVE_FUNCTION(fc_solve_sfs_simple_simon_move_sequence_to_true_parent);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_whole_stack_sequence_to_false_parent);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_sequence_to_true_parent_with_some_cards_above);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_sequence_with_some_cards_above_to_true_parent);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_sequence_with_junk_seq_above_to_true_parent_with_some_cards_above);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_whole_stack_sequence_to_false_parent_with_some_cards_above);

DECLARE_MOVE_FUNCTION(
    fc_solve_sfs_simple_simon_move_sequence_to_parent_on_the_same_stack);

DECLARE_MOVE_FUNCTION(fc_solve_sfs_simple_simon_move_sequence_to_false_parent);

#endif /* #ifndef FCS_DISABLE_SIMPLE_SIMON */

#ifdef __cplusplus
}
#endif
