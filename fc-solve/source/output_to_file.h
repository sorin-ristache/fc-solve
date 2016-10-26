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
 * output_to_file.h - header file for outputting a solution to a file.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include "rinutils.h"
#include "fcs_enums.h"
#include "fcs_user.h"

typedef struct
{
    const char *output_filename;
    int standard_notation;
    fcs_bool_t debug_iter_state_output;
#ifndef FC_SOLVE_IMPLICIT_PARSABLE_OUTPUT
    fcs_bool_t parseable_output;
#endif
    fcs_bool_t canonized_order_output;
#ifndef FC_SOLVE_IMPLICIT_T_RANK
    fcs_bool_t display_10_as_t;
#endif
    fcs_bool_t display_parent_iter_num;
    fcs_bool_t debug_iter_output_on;
    fcs_bool_t display_moves;
    fcs_bool_t display_states;
    fcs_bool_t show_exceeded_limits;
} fc_solve_display_information_context_t;

static const fc_solve_display_information_context_t INITIAL_DISPLAY_CONTEXT = {
    .debug_iter_state_output = FALSE,
#ifndef FC_SOLVE_IMPLICIT_PARSABLE_OUTPUT
    .parseable_output = FALSE,
#endif
    .canonized_order_output = FALSE,
#ifndef FC_SOLVE_IMPLICIT_T_RANK
    .display_10_as_t = FALSE,
#endif
    .display_parent_iter_num = FALSE,
    .display_moves = FALSE,
    .display_states = TRUE,
    .standard_notation = FC_SOLVE__STANDARD_NOTATION_NO,
    .output_filename = NULL,
    .show_exceeded_limits = FALSE};

static GCC_INLINE void fc_solve_output_result_to_file(FILE *const output_fh,
    void *const instance, const int ret,
    const fc_solve_display_information_context_t *const dc_ptr)
{
    const_AUTO(display_context, (*dc_ptr));
    if (ret == FCS_STATE_WAS_SOLVED)
    {
        fprintf(output_fh, "-=-=-=-=-=-=-=-=-=-=-=-\n\n");
        {
            fcs_move_t move;
            FILE *move_dump;
            char as_string[1000];

            move_dump = output_fh;

            if (display_context.display_states)
            {
                freecell_solver_user_current_state_stringify(
                    instance, as_string FC_SOLVE__PASS_PARSABLE(
                                  display_context.parseable_output),
                    display_context.canonized_order_output FC_SOLVE__PASS_T(
                        display_context.display_10_as_t));

                fprintf(move_dump, "%s\n", as_string);
                fprintf(move_dump, "%s", "\n====================\n\n");
            }

            int move_num = 0;
            while (freecell_solver_user_get_next_move(instance, &move) == 0)
            {
                if (display_context.display_moves)
                {
                    if (display_context.display_states &&
                        display_context.standard_notation)
                    {
                        fprintf(move_dump, "Move: ");
                    }

                    freecell_solver_user_stringify_move_w_state(instance,
                        as_string, move, display_context.standard_notation);
                    fprintf(move_dump,
                        (display_context.standard_notation ? "%s " : "%s\n"),
                        as_string);
                    move_num++;
                    if (display_context.standard_notation)
                    {
                        if ((move_num % 10 == 0) ||
                            display_context.display_states)
                        {
                            fprintf(move_dump, "\n");
                        }
                    }
                    if (display_context.display_states)
                    {
                        fprintf(move_dump, "\n");
                    }
                    fflush(move_dump);
                }

                if (display_context.display_states)
                {
                    freecell_solver_user_current_state_stringify(
                        instance, as_string FC_SOLVE__PASS_PARSABLE(
                                      display_context.parseable_output),
                        display_context.canonized_order_output FC_SOLVE__PASS_T(
                            display_context.display_10_as_t));

                    fprintf(move_dump, "%s\n", as_string);
                }

                if (display_context.display_states ||
                    (!display_context.standard_notation))
                {
                    fprintf(move_dump, "%s", "\n====================\n\n");
                }
            }

            if (display_context.standard_notation &&
                (!display_context.display_states))
            {
                fprintf(move_dump, "\n\n");
            }
        }

        fprintf(output_fh, "This game is solveable.\n");
    }
    else if (display_context.show_exceeded_limits &&
             (ret == FCS_STATE_SUSPEND_PROCESS))
    {
        fprintf(output_fh, "Iterations count exceeded.\n");
    }
    else
    {
        fprintf(output_fh, "I could not solve this game.\n");
    }

    fprintf(output_fh, "Total number of states checked is %li.\n",
        (long)freecell_solver_user_get_num_times_long(instance));
#if 1
    fprintf(output_fh, "This scan generated %li states.\n",
        (long)freecell_solver_user_get_num_states_in_collection_long(instance));
#endif

    return;
}

#ifdef __cplusplus
}
#endif
