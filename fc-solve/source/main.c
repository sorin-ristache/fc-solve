/* Copyright (c) 2000 Shlomi Fish
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */
/*
 * main.c - the main() and related functions of the fc-solve command line
 * executable.
 *
 * It is documented in the documents "README", "USAGE", etc. in the
 * Freecell Solver distribution from http://fc-solve.shlomifish.org/ .
 */
#include "cl_callback.h"

int main(int argc, char * argv[])
{
    FILE * file;
    char user_state[USER_STATE_SIZE];

    fc_solve_display_information_context_t debug_context = INITIAL_DISPLAY_CONTEXT;

    dc = &debug_context;

    int arg = 1;
    void * const instance = alloc_instance_and_parse(
        argc,
        argv,
        &arg,
        known_parameters,
        fc_solve__cmd_line_callback,
        &debug_context,
        FALSE
    );

    current_instance = instance;

    if ((arg == argc) || (!strcmp(argv[arg], "-")))
    {
        file = stdin;
        if (!getenv("FREECELL_SOLVER_QUIET"))
        {
            fprintf(stderr, "%s",
                    "Reading the board from the standard input.\n"
                    "Please refer to the documentation for more usage information:\n"
                    "    http://fc-solve.shlomifish.org/docs/\n"
                    "To cancel this message set the FREECELL_SOLVER_QUIET environment variable.\n"
                   );
        }
    }
    else if (argv[arg][0] == '-')
    {
        fprintf(stderr,
                "Unknown option \"%s\". "
                "Type \"%s --help\" for usage information.\n",
                argv[arg],
                argv[0]
                );
        freecell_solver_user_free(instance);

        return -1;
    }
    else
    {
        file = fopen(argv[arg], "r");
        if (file == NULL)
        {
            fprintf(stderr,
                "Could not open file \"%s\" for input. Exiting.\n",
                argv[arg]
                );
            freecell_solver_user_free(instance);

            return -1;
        }
    }
    memset(user_state, '\0', sizeof(user_state));
    fread(user_state, sizeof(user_state[0]), USER_STATE_SIZE-1, file);
    fclose(file);

    /* Win32 Does not have those signals */
#ifndef WIN32
    signal(SIGUSR1, command_signal_handler);
    signal(SIGUSR2, select_signal_handler);
    signal(SIGABRT, abort_signal_handler);
#endif

#if 0
    int ret;
    {
        fcs_int_limit_t limit = 500;
        freecell_solver_user_limit_iterations_long(instance, limit);
        ret = freecell_solver_user_solve_board(instance, user_state);
        while (ret == FCS_STATE_SUSPEND_PROCESS)
        {
            limit += 500;
            freecell_solver_user_limit_iterations_long(instance, limit);
            ret = freecell_solver_user_resume_solution(instance);
        }
    }
#else
    int ret = freecell_solver_user_solve_board(instance, user_state);
#endif

    exit_code_t exit_code = SUCCESS;
    switch (ret)
    {
        case FCS_STATE_INVALID_STATE:
        {
        char error_string[80];

        freecell_solver_user_get_invalid_state_error_into_string(
            instance,
            error_string
            FC_SOLVE__PASS_T(debug_context.display_10_as_t)
        );
        fprintf(stderr, "%s\n", error_string);
        exit_code = ERROR;
        }
        break;

        case FCS_STATE_FLARES_PLAN_ERROR:
        fprintf(stderr, "Flares Plan: %s\n", freecell_solver_user_get_last_error_string(instance));
        exit_code = ERROR;
        break;

        default:
        {
        FILE * output_fh;

        if (debug_context.output_filename)
        {
            output_fh = fopen(debug_context.output_filename, "wt");
            if (! output_fh)
            {
                fprintf(stderr,
                        "Could not open output file '%s' for writing!",
                        debug_context.output_filename
                       );
                return -1;
            }
        }
        else
        {
            output_fh = stdout;
        }

        fc_solve_output_result_to_file(
            output_fh, instance, ret, &debug_context
        );

        if (debug_context.output_filename)
        {
            fclose(output_fh);
            output_fh = NULL;
        }
        }
        break;
    }

    freecell_solver_user_free(instance);

    return exit_code;
}

