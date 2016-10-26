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
 * str_utils.h - string utilities.
 */
#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include "inline.h"
#include "bool.h"
#include <string.h>

static GCC_INLINE fcs_bool_t string_starts_with(
    const char *const str, const char *const prefix, const char *const end)
{
    register const size_t check_len = (size_t)(end - str);

    return (
        (check_len == strlen(prefix)) && (!strncmp(str, prefix, check_len)));
}

static GCC_INLINE const char *try_str_prefix(
    const char *const str, const char *const prefix)
{
    register const size_t len = strlen(prefix);

    return (strncmp(str, prefix, len) ? NULL : str + len);
}

#ifdef __cplusplus
};
#endif
