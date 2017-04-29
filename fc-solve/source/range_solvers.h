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
 * range_solvers.h - common routines for the range solvers.
 */
#pragma once
#include "rinutils.h"
#include "fcs_cl.h"
#include "range_solvers_gen_ms_boards.h"
#include "handle_parsing.h"
#include "help_err.h"

static inline fcs_bool_t range_solvers__solve(void *const instance,
    const long long board_num, fcs_int_limit_t *const total_num_iters_temp)
{
    fcs_state_string_t state_string;
    get_board(board_num, state_string);

    switch (freecell_solver_user_solve_board(instance, state_string))
    {
    case FCS_STATE_SUSPEND_PROCESS:
        fc_solve_print_intractable(board_num);
        break;

    case FCS_STATE_FLARES_PLAN_ERROR:
        print_flares_plan_error(instance);
        return TRUE;

    case FCS_STATE_IS_NOT_SOLVEABLE:
        fc_solve_print_unsolved(board_num);
        break;
    }

    *total_num_iters_temp += freecell_solver_user_get_num_times_long(instance);
    return FALSE;
}