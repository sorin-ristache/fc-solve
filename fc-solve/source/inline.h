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
 * inline.h - the purpose of this file is to define the GCC_INLINE
 * macro.
 */
#pragma once

#include "config.h"

#if defined(HAVE_C_INLINE)
#define GCC_INLINE FCS_INLINE_KEYWORD
#elif defined(__GNUC__)
#define GCC_INLINE inline
#else
#define GCC_INLINE
#endif
