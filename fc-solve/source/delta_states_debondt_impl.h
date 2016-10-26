/*
 * This file is part of Freecell Solver. It is subject to the license terms in
 * the COPYING.txt file found in the top-level directory of this distribution
 * and at http://fc-solve.shlomifish.org/docs/distro/COPYING.html . No part of
 * Freecell Solver, including this file, may be copied, modified, propagated,
 * or distributed except according to the terms contained in the COPYING file.
 *
 * Copyright (c) 2011 Shlomi Fish
 */
/*
 * delta_states_debondt_impl.h - "delta states" are an encoding of states,
 * where the states are encoded and decoded based on a compact delta from the
 * initial state.
 *
 * This encoding improves upon the original delta_states.c .
 */

#include "dll_thunk.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "bit_rw.h"
#include "state.h"
#include "indirect_buffer.h"
#include "delta_states_iface.h"
#include "delta_states.h"
#include "delta_states_debondt.h"
#include "debondt_delta_states_iface.h"
#include "var_base_reader.h"
#include "var_base_writer.h"

#ifdef FCS_COMPILE_DEBUG_FUNCTIONS
#include "dbm_common.h"
#endif

#define FOUNDATION_BASE (RANK_KING + 1)

enum
{
    OPT_TOPMOST = 0,
    OPT_DONT_CARE = OPT_TOPMOST,
    OPT_FREECELL = 1,
    OPT_ORIG_POS = 2,
    NUM_KING_OPTS = 3,
    OPT_PARENT_SUIT_MOD_IS_0 = 3,
    OPT_PARENT_SUIT_MOD_IS_1 = 4,
    NUM_OPTS = 5,
    OPT_IN_FOUNDATION = 5,
    OPT__BAKERS_DOZEN__ORIG_POS = 0,
    OPT__BAKERS_DOZEN__FIRST_PARENT = 1,
    NUM__BAKERS_DOZEN__OPTS = OPT__BAKERS_DOZEN__FIRST_PARENT + 4,
    OPT__BAKERS_DOZEN__IN_FOUNDATION = NUM__BAKERS_DOZEN__OPTS,
};

#define IS_BAKERS_DOZEN() (local_variant == FCS_DBM_VARIANT_BAKERS_DOZEN)

static void fc_solve_debondt_delta_stater_init(
    fc_solve_debondt_delta_stater_t *const self,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_state_t *const init_state, const int num_columns,
    const int num_freecells
#ifndef FCS_FREECELL_ONLY
    ,
    const int sequences_are_built_by
#endif
    )
{
#ifndef FCS_FREECELL_ONLY
    self->sequences_are_built_by = sequences_are_built_by;
#endif

    self->num_columns = num_columns;
    self->num_freecells = num_freecells;

    self->_init_state = init_state;

    memset(self->bakers_dozen_topmost_cards_lookup, '\0',
        sizeof(self->bakers_dozen_topmost_cards_lookup));

    fc_solve_var_base_writer_init(&self->w);
    fc_solve_var_base_reader_init(&self->r);

    if (IS_BAKERS_DOZEN())
    {
        for (int col_idx = 0; col_idx < self->num_columns; col_idx++)
        {
            const fcs_cards_column_t col =
                fcs_state_get_col(*init_state, col_idx);
            const int col_len = fcs_col_len(col);

            if (col_len > 0)
            {
#ifndef DEBUG_STATES
                const fcs_card_t top_card = fcs_col_get_card(col, 0);
#else
                const fcs_card_t top_card_proto = fcs_col_get_card(col, 0);
                const unsigned char top_card =
                    (top_card_proto.suit | (top_card_proto.rank << 2));
#endif
                self->bakers_dozen_topmost_cards_lookup[top_card >> 3] |=
                    (1 << top_card & (8 - 1));
            }
        }
    }
}

static GCC_INLINE void fc_solve_debondt_delta_stater__init_card_states(
    fc_solve_debondt_delta_stater_t *const self)
{
    int *const card_states = self->card_states;
    for (size_t i = 0; i < COUNT(self->card_states); i++)
    {
        card_states[i] = -1;
    }
}

static GCC_INLINE void fc_solve_debondt_delta_stater_release(
    fc_solve_debondt_delta_stater_t *const self)
{
    fc_solve_var_base_reader_release(&(self->r));
    fc_solve_var_base_writer_release(&(self->w));
}

static GCC_INLINE void fc_solve_debondt_delta_stater_set_derived(
    fc_solve_debondt_delta_stater_t *const self, fcs_state_t *const state)
{
    self->_derived_state = state;
}

#define GET_SUIT_BIT(card) (((fcs_card_suit(card)) & 0x2) >> 1)

static GCC_INLINE int wanted_suit_bit_opt(const fcs_card_t parent_card)
{
    return GET_SUIT_BIT(parent_card) ? OPT_PARENT_SUIT_MOD_IS_1
                                     : OPT_PARENT_SUIT_MOD_IS_0;
}

static GCC_INLINE int wanted_suit_idx_opt(const fcs_card_t parent_card)
{
    return OPT__BAKERS_DOZEN__FIRST_PARENT + fcs_card_suit(parent_card);
}

static GCC_INLINE int calc_child_card_option(
    const enum fcs_dbm_variant_type_t local_variant,
    const fcs_card_t parent_card, const fcs_card_t child_card
#ifndef FCS_FREECELL_ONLY
    ,
    const int sequences_are_built_by
#endif
    )
{
    if (IS_BAKERS_DOZEN())
    {
        if ((fcs_card_rank(child_card) != 1) &&
            (fcs_card_rank(child_card) + 1 == fcs_card_rank(parent_card)))
        {
            return wanted_suit_idx_opt(parent_card);
        }
        else
        {
            return OPT__BAKERS_DOZEN__ORIG_POS;
        }
    }
    else
    {
        if ((fcs_card_rank(child_card) != 1) &&
            (fcs_is_parent_card(child_card, parent_card)))
        {
            return wanted_suit_bit_opt(parent_card);
        }
        else
        {
            return OPT_ORIG_POS;
        }
    }
}

static GCC_INLINE int get_top_rank_for_iter(
    const enum fcs_dbm_variant_type_t local_variant)
{
    return (IS_BAKERS_DOZEN() ? (RANK_KING - 1) : RANK_KING);
}

#define NUM_SUITS 4
static void fc_solve_debondt_delta_stater_encode_composite(
    fc_solve_debondt_delta_stater_t *const self,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_var_base_writer_t *const writer)
{
    fcs_state_t *const derived = self->_derived_state;

    fc_solve_debondt_delta_stater__init_card_states(self);

    {
        for (int suit_idx = 0; suit_idx < NUM_SUITS; suit_idx++)
        {
            const unsigned long rank = fcs_foundation_value(*derived, suit_idx);

            fc_solve_var_base_writer_write(writer, FOUNDATION_BASE, rank);

            const unsigned long max_rank = ((rank < 1) ? 1 : rank);

            for (unsigned long r = 1; r <= max_rank; r++)
            {
#define STATE_POS(suit_idx, rank) (rank - 1 + suit_idx * RANK_KING)
#define CARD_POS(card) (STATE_POS((fcs_card_suit(card)), (fcs_card_rank(card))))
                self->card_states[STATE_POS(suit_idx, r)] = OPT_DONT_CARE;
            }
        }
    }

    {
        for (int fc_idx = 0; fc_idx < self->num_freecells; fc_idx++)
        {
            const fcs_card_t card = fcs_freecell_card(*derived, fc_idx);

            if (fcs_card_is_valid(card))
            {
                self->card_states[CARD_POS(card)] = OPT_FREECELL;
            }
        }
    }

    if (IS_BAKERS_DOZEN())
    {
        for (int col_idx = 0; col_idx < self->num_columns; col_idx++)
        {
            const fcs_cards_column_t col = fcs_state_get_col(*derived, col_idx);
            const int col_len = fcs_col_len(col);

            if (col_len > 0)
            {
                const fcs_card_t top_card = fcs_col_get_card(col, 0);

                /* Skip Aces which were already set. */
                if (fcs_card_rank(top_card) != 1)
                {
                    self->card_states[CARD_POS(top_card)] =
                        OPT__BAKERS_DOZEN__ORIG_POS;
                }

                for (int pos = 1; pos < col_len; pos++)
                {
                    const fcs_card_t parent_card =
                        fcs_col_get_card(col, pos - 1);
                    const fcs_card_t this_card = fcs_col_get_card(col, pos);

                    /* Skip Aces which were already set. */
                    if (fcs_card_rank(this_card) != 1)
                    {
                        if (fcs_card_rank(this_card) + 1 ==
                            fcs_card_rank(parent_card))
                        {
                            self->card_states[CARD_POS(this_card)] =
                                wanted_suit_idx_opt(parent_card);
                        }
                        else
                        {
                            self->card_states[CARD_POS(this_card)] =
                                OPT__BAKERS_DOZEN__ORIG_POS;
                        }
                    }
                }
            }
        }
    }
    else
    {
        for (int col_idx = 0; col_idx < self->num_columns; col_idx++)
        {
            const fcs_cards_column_t col = fcs_state_get_col(*derived, col_idx);
            const int col_len = fcs_col_len(col);

            if (col_len > 0)
            {
                fcs_card_t top_card = fcs_col_get_card(col, 0);

                if (fcs_card_rank(top_card) != 1)
                {
                    self->card_states[CARD_POS(top_card)] = OPT_TOPMOST;
                }

                fcs_card_t parent_card = top_card;

                for (int child_idx = 1; child_idx < col_len; child_idx++)
                {
                    const fcs_card_t child_card =
                        fcs_col_get_card(col, child_idx);

                    if (fcs_card_rank(child_card) != 1)
                    {
                        self->card_states[CARD_POS(child_card)] =
                            calc_child_card_option(
                                local_variant, parent_card, child_card
#ifndef FCS_FREECELL_ONLY
                                ,
                                self->sequences_are_built_by
#endif
                                );
                    }

                    parent_card = child_card;
                }
            }
        }
    }

    /*
     * All cards should be determined now - let's encode.
     *
     * The foundations have already been encoded.
     *
     * Skip encoding the aces, and the kings are encoded with less bits.
     */
    {
        const int top_rank_for_iter = get_top_rank_for_iter(local_variant);
        for (int rank = 2; rank <= top_rank_for_iter; rank++)
        {
            for (int suit_idx = 0; suit_idx < NUM_SUITS; suit_idx++)
            {
                const unsigned long opt =
                    self->card_states[STATE_POS(suit_idx, rank)];
                unsigned long base;

                if (IS_BAKERS_DOZEN())
                {
                    char card = fcs_card2char(fcs_make_card(rank, suit_idx));

                    if (self->bakers_dozen_topmost_cards_lookup[card >> 3] &
                        (1 << (card & (8 - 1))))
                    {
                        continue;
                    }
                    base = NUM__BAKERS_DOZEN__OPTS;
                }
                else
                {
                    base = ((rank == RANK_KING) ? NUM_KING_OPTS : NUM_OPTS);
                }

                assert(opt < base);

                fc_solve_var_base_writer_write(writer, base, opt);
            }
        }
    }
}

static GCC_INLINE void
fc_solve_debondt_delta_stater__fill_column_with_descendent_cards(
    fc_solve_debondt_delta_stater_t *const self,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_cards_column_t *const col)
{
    fcs_card_t parent_card = fcs_col_get_card(*col, fcs_col_len(*col) - 1);

    while (fcs_card_is_valid(parent_card))
    {
        const int wanted_opt =
            (IS_BAKERS_DOZEN() ? wanted_suit_idx_opt(parent_card)
                               : wanted_suit_bit_opt(parent_card));

        fcs_card_t child_card = fc_solve_empty_card;
        const int candidate_rank = fcs_card_rank(parent_card) - 1;
        for (int suit = (IS_BAKERS_DOZEN()
                             ? 0
                             : ((fcs_card_suit(parent_card) & (0x1)) ^ 0x1));
             suit < NUM_SUITS; suit += (IS_BAKERS_DOZEN() ? 1 : 2))
        {
            const fcs_card_t candidate_card =
                fcs_make_card(candidate_rank, suit);

            if (self->card_states[CARD_POS(candidate_card)] == wanted_opt)
            {
                child_card = candidate_card;
                break;
            }
        }

        if (fcs_card_is_valid(child_card))
        {
            fcs_col_push_card(*col, child_card);
        }
        parent_card = child_card;
    }
}

static void fc_solve_debondt_delta_stater_decode(
    fc_solve_debondt_delta_stater_t *const self,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_var_base_reader_t *const reader, fcs_state_t *const ret)
{
    unsigned char orig_top_most_cards[4 * RANK_KING];
    fcs_card_t new_top_most_cards[MAX_NUM_STACKS];

    fc_solve_debondt_delta_stater__init_card_states(self);

    {
        for (int suit_idx = 0; suit_idx < NUM_SUITS; suit_idx++)
        {
            const unsigned long foundation_rank =
                fc_solve_var_base_reader_read(reader, FOUNDATION_BASE);

            for (unsigned long rank = 1; rank <= foundation_rank; rank++)
            {
                self->card_states[STATE_POS(suit_idx, rank)] =
                    (IS_BAKERS_DOZEN() ? OPT__BAKERS_DOZEN__IN_FOUNDATION
                                       : OPT_IN_FOUNDATION);
            }

            fcs_set_foundation(*ret, suit_idx, foundation_rank);
        }
    }

#define IS_IN_FOUNDATIONS(card)                                                \
    (fcs_card_rank(card) <= fcs_foundation_value(*ret, fcs_card_suit(card)))

    fcs_state_t *const init_state = self->_init_state;

    const int orig_pos_opt =
        (IS_BAKERS_DOZEN() ? OPT__BAKERS_DOZEN__ORIG_POS : OPT_ORIG_POS);

    const int num_freecells = self->num_freecells;

    memset(orig_top_most_cards, '\0', sizeof(orig_top_most_cards));
    {
        for (int col_idx = 0; col_idx < self->num_columns; col_idx++)
        {
            const fcs_cards_column_t col =
                fcs_state_get_col(*init_state, col_idx);

            if (fcs_col_len(col))
            {
                const fcs_card_t card = fcs_col_get_card(col, 0);
                orig_top_most_cards[CARD_POS(card)] = 1;
            }
        }
    }

    /* Process the kings: */
    if (IS_BAKERS_DOZEN())
    {
        for (int suit_idx = 0; suit_idx < NUM_SUITS; suit_idx++)
        {
            fcs_card_t card = fcs_make_card(RANK_KING, suit_idx);

            if (!IS_IN_FOUNDATIONS(card))
            {
                self->card_states[CARD_POS(card)] = OPT__BAKERS_DOZEN__ORIG_POS;
            }
        }
    }

    int next_freecell_idx = 0;
    int next_new_top_most_cards = 0;
    const int top_rank_for_iter = get_top_rank_for_iter(local_variant);
    for (int rank = 1; rank <= top_rank_for_iter; rank++)
    {
        for (int suit_idx = 0; suit_idx < NUM_SUITS; suit_idx++)
        {
            const fcs_card_t card = fcs_make_card(rank, suit_idx);
            const char card_char = fcs_card2char(card);

            if (IS_BAKERS_DOZEN())
            {
                if ((self->bakers_dozen_topmost_cards_lookup[card_char >> 3] &
                        (1 << (card_char & (8 - 1)))))
                {
                    if (!IS_IN_FOUNDATIONS(card))
                    {
                        self->card_states[CARD_POS(card)] =
                            OPT__BAKERS_DOZEN__ORIG_POS;
                    }
                    continue;
                }
            }

            const int existing_opt =
                self->card_states[STATE_POS(suit_idx, rank)];

            if (rank == 1)
            {
                if (existing_opt < 0)
                {
                    self->card_states[STATE_POS(suit_idx, rank)] = orig_pos_opt;
                }
            }
            else
            {
                const unsigned long base =
                    (IS_BAKERS_DOZEN()
                            ? NUM__BAKERS_DOZEN__OPTS
                            : ((rank == RANK_KING) ? NUM_KING_OPTS : NUM_OPTS));
                const unsigned long item_opt =
                    fc_solve_var_base_reader_read(reader, base);

                if (existing_opt < 0)
                {
                    self->card_states[STATE_POS(suit_idx, rank)] = item_opt;

                    if (!IS_BAKERS_DOZEN())
                    {
                        if (item_opt == OPT_FREECELL)
                        {
                            fcs_put_card_in_freecell(
                                *ret, next_freecell_idx, card);
                            next_freecell_idx++;
                        }
                        else if (item_opt == OPT_TOPMOST)
                        {
                            if (!orig_top_most_cards[CARD_POS(card)])
                            {
                                new_top_most_cards[next_new_top_most_cards++] =
                                    card;
                            }
                        }
                    }
                }
            }
        }
    }

    for (; next_freecell_idx < num_freecells; next_freecell_idx++)
    {
        fcs_empty_freecell(*ret, next_freecell_idx);
    }

    {
        for (int col_idx = 0; col_idx < self->num_columns; col_idx++)
        {
            fcs_card_t top_card;
            int top_opt;

            fcs_cards_column_t col = fcs_state_get_col(*ret, col_idx);
            const fcs_cards_column_t orig_col =
                fcs_state_get_col(*init_state, col_idx);

            if (fcs_col_len(orig_col))
            {
                top_card = fcs_col_get_card(orig_col, 0);
                top_opt = self->card_states[CARD_POS(top_card)];
            }
            else
            {
                top_card = fc_solve_empty_card;
                top_opt = -1;
            }

            if (fcs_card_is_empty(top_card) ||
                (!((top_opt == OPT_TOPMOST) || (top_opt == orig_pos_opt))))
            {
                if (next_new_top_most_cards > 0)
                {
                    fcs_col_push_card(
                        col, new_top_most_cards[--next_new_top_most_cards]);

                    fc_solve_debondt_delta_stater__fill_column_with_descendent_cards(
                        self, local_variant, &col);
                }
            }
            else
            {
                fcs_card_t parent_card;
                int pos;

                fcs_col_push_card(col, top_card);

                parent_card = top_card;

                for (pos = 1; pos < fcs_col_len(orig_col); pos++)
                {
                    fcs_card_t child_card;

                    child_card = fcs_col_get_card(orig_col, pos);

                    if ((!IS_IN_FOUNDATIONS(child_card)) &&
                        (self->card_states[CARD_POS(child_card)] ==
                            calc_child_card_option(
                                local_variant, parent_card, child_card
#ifndef FCS_FREECELL_ONLY
                                ,
                                self->sequences_are_built_by
#endif
                                )))
                    {
                        fcs_col_push_card(col, child_card);
                        parent_card = child_card;
                    }
                    else
                    {
                        break;
                    }
                }

                fc_solve_debondt_delta_stater__fill_column_with_descendent_cards(
                    self, local_variant, &col);
            }
        }
    }
#undef IS_IN_FOUNDATIONS
}

static GCC_INLINE void fc_solve_debondt_delta_stater_decode_into_state_proto(
    const enum fcs_dbm_variant_type_t local_variant,
    fc_solve_debondt_delta_stater_t *const delta_stater,
    const fcs_uchar_t *const enc_state,
    fcs_state_keyval_pair_t *const ret IND_BUF_T_PARAM(indirect_stacks_buffer))
{
    fc_solve_var_base_reader_start(
        &(delta_stater->r), enc_state, sizeof(fcs_encoded_state_buffer_t));

    fc_solve_state_init(ret, STACKS_NUM, indirect_stacks_buffer);

    fc_solve_debondt_delta_stater_decode(
        delta_stater, local_variant, &(delta_stater->r), &(ret->s));
}

#ifdef INDIRECT_STACK_STATES
#define fc_solve_debondt_delta_stater_decode_into_state(                       \
    local_variant, delta_stater, enc_state, state_ptr, indirect_stacks_buffer) \
    fc_solve_debondt_delta_stater_decode_into_state_proto(local_variant,       \
        delta_stater, enc_state, state_ptr, indirect_stacks_buffer)
#else
#define fc_solve_debondt_delta_stater_decode_into_state(                       \
    local_variant, delta_stater, enc_state, state_ptr, indirect_stacks_buffer) \
    fc_solve_debondt_delta_stater_decode_into_state_proto(                     \
        local_variant, delta_stater, enc_state, state_ptr)
#endif

static GCC_INLINE void fc_solve_debondt_delta_stater_encode_into_buffer(
    fc_solve_debondt_delta_stater_t *const delta_stater,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_state_keyval_pair_t *const state, unsigned char *const out_enc_state)
{
    fc_solve_var_base_writer_start(&(delta_stater->w));
    fc_solve_debondt_delta_stater_set_derived(delta_stater, &(state->s));
    fc_solve_debondt_delta_stater_encode_composite(
        delta_stater, local_variant, &(delta_stater->w));
    fc_solve_var_base_writer_get_data(&(delta_stater->w), out_enc_state);
}

static GCC_INLINE void fcs_debondt_init_and_encode_state(
    fc_solve_debondt_delta_stater_t *const delta_stater,
    const enum fcs_dbm_variant_type_t local_variant,
    fcs_state_keyval_pair_t *const state,
    fcs_encoded_state_buffer_t *const enc_state)
{
    fcs_init_encoded_state(enc_state);

    fc_solve_debondt_delta_stater_encode_into_buffer(
        delta_stater, local_variant, state, enc_state->s);
}

#undef IS_BAKERS_DOZEN
