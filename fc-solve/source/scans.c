/*
 * This file is part of Freecell Solver. It is subject to the license terms in
 * the COPYING.txt file found in the top-level directory of this distribution
 * and at http://fc-solve.shlomifish.org/docs/distro/COPYING.html . No part of
 * Freecell Solver, including this file, may be copied, modified, propagated,
 * or distributed except according to the terms contained in the COPYING file.
 *
 * Copyright (c) 2000 Shlomi Fish
 */
// scans.c - The code that relates to the various scans.
// Currently Soft-DFS / Random-DFS, Best-FS and Breadth-FS are implemented.

#include "scans.h"
#include "meta_alloc.h"
#include "move_stack_compact_alloc.h"

#undef DEBUG

#include "scans_impl.h"

/* GCC does not handle inline functions as well as macros. */
#define kv_calc_depth(ptr_state)                                               \
    calc_depth(FCS_STATE_kv_to_collectible(ptr_state))

#ifdef FCS_RCS_STATES
// TODO : Unit-test this function as it had had a bug beforehand
// because lru_side had been an unsigned long.
typedef const char *lru_side;

extern int __attribute__((pure))
fc_solve_compare_lru_cache_keys(const void *const void_a,
    const void *const void_b, void *const context GCC_UNUSED)
{
#define GET_PARAM(p) ((lru_side)(((const fcs_cache_key_info *)(p))->val_ptr))
    const lru_side a = GET_PARAM(void_a), b = GET_PARAM(void_b);

    return ((a > b) ? 1 : (a < b) ? (-1) : 0);
#undef GET_PARAM
}

#define NEXT_CACHE_STATE(s) ((s)->lower_pri)
fcs_state *fc_solve_lookup_state_key_from_val(fcs_instance *const instance,
    const fcs_collectible_state *const orig_ptr_state_val)
{
#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
    PWord_t PValue;
#endif
    FC__STACKS__SET_PARAMS();
    fcs_lru_cache *cache = &(instance->rcs_states_cache);

    ssize_t parents_stack_len = 1;
    ssize_t parents_stack_max_len = 16;

    struct
    {
        fcs_cache_key_info *new_cache_state;
        const fcs_collectible_state *state_val;
    } *parents_stack = SMALLOC(parents_stack, (size_t)parents_stack_max_len);

    parents_stack[0].state_val = orig_ptr_state_val;

    fcs_cache_key_info *new_cache_state;
    while (1)
    {
#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
        JLI(PValue, cache->states_values_to_keys_map,
            ((Word_t)parents_stack[parents_stack_len - 1].state_val));
        if (*PValue)
        {
            parents_stack[parents_stack_len - 1].new_cache_state =
                new_cache_state = (fcs_cache_key_info *)(*PValue);
            break;
        }
        else
        {
            /* A new state. */
            if (cache->recycle_bin)
            {
                new_cache_state = cache->recycle_bin;
                cache->recycle_bin = NEXT_CACHE_STATE(new_cache_state);
            }
            else
            {
                new_cache_state = fcs_compact_alloc_ptr(
                    &(cache->states_values_to_keys_allocator),
                    sizeof(*new_cache_state));
            }
        }
#else
        if (cache->recycle_bin)
        {
            new_cache_state = cache->recycle_bin;
            cache->recycle_bin = NEXT_CACHE_STATE(new_cache_state);
        }
        else
        {
            new_cache_state =
                fcs_compact_alloc_ptr(&(cache->states_values_to_keys_allocator),
                    sizeof(*new_cache_state));
        }

        new_cache_state->val_ptr =
            parents_stack[parents_stack_len - 1].state_val;
        fcs_cache_key_info *const existing_cache_state =
            (fcs_cache_key_info *)fc_solve_kaz_tree_alloc_insert(
                cache->kaz_tree, new_cache_state);

        if (existing_cache_state)
        {
            NEXT_CACHE_STATE(new_cache_state) = cache->recycle_bin;
            cache->recycle_bin = new_cache_state;

            parents_stack[parents_stack_len - 1].new_cache_state =
                new_cache_state = existing_cache_state;
            break;
        }
#endif

        parents_stack[parents_stack_len - 1].new_cache_state = new_cache_state;

#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
        *PValue = ((Word_t)new_cache_state);

        new_cache_state->val_ptr =
            parents_stack[parents_stack_len - 1].state_val;
#endif
        new_cache_state->lower_pri = new_cache_state->higher_pri = NULL;
        ++cache->count_elements_in_cache;

        if (!FCS_S_PARENT(parents_stack[parents_stack_len - 1].state_val))
        {
            new_cache_state->key = instance->state_copy.s;
            break;
        }
        else
        {
            parents_stack[parents_stack_len].state_val =
                FCS_S_PARENT(parents_stack[parents_stack_len - 1].state_val);
            if (++parents_stack_len == parents_stack_max_len)
            {
                parents_stack_max_len += 16;
                const_AUTO(old_parents_stack, parents_stack);
                parents_stack =
                    SREALLOC(parents_stack, (size_t)parents_stack_max_len);
                if (unlikely(!parents_stack))
                {
                    free(old_parents_stack);
                }
            }
        }
    }

    for (--parents_stack_len; parents_stack_len > 0; --parents_stack_len)
    {
        new_cache_state = parents_stack[parents_stack_len - 1].new_cache_state;

        fcs_state *const pass_key = &(new_cache_state->key);
        *pass_key = parents_stack[parents_stack_len].new_cache_state->key;

        const fcs_move_stack *const stack_ptr__moves_to_parent =
            parents_stack[parents_stack_len - 1].state_val->moves_to_parent;
        const fcs_internal_move *next_move = stack_ptr__moves_to_parent->moves;
        const fcs_internal_move *const moves_end =
            (next_move + stack_ptr__moves_to_parent->num_moves);

        for (; next_move < moves_end; next_move++)
        {
            fc_solve_apply_move(pass_key, NULL,
                (*next_move)PASS_FREECELLS(LOCAL_FREECELLS_NUM)
                    PASS_STACKS(LOCAL_STACKS_NUM));
        }
        /* The state->parent_state moves stack has an implicit canonize
         * suffix move. */
        fc_solve_canonize_state(pass_key PASS_FREECELLS(LOCAL_FREECELLS_NUM)
                PASS_STACKS(LOCAL_STACKS_NUM));

        /* Promote new_cache_state to the head of the priority list. */
        if (!cache->lowest_pri)
        {
            /* It's the only state. */
            cache->lowest_pri = new_cache_state;
            cache->highest_pri = new_cache_state;
        }
        else
        {
            /* First remove the state from its place in the doubly-linked
             * list by linking its neighbours together.
             * */
            if (new_cache_state->higher_pri)
            {
                new_cache_state->higher_pri->lower_pri =
                    new_cache_state->lower_pri;
            }

            if (new_cache_state->lower_pri)
            {
                new_cache_state->lower_pri->higher_pri =
                    new_cache_state->higher_pri;
            }
            /* Bug fix: make sure that ->lowest_pri is always valid. */
            else if (new_cache_state->higher_pri)
            {
                cache->lowest_pri = new_cache_state->higher_pri;
            }

            /* Now promote it to be the highest. */
            cache->highest_pri->higher_pri = new_cache_state;
            new_cache_state->lower_pri = cache->highest_pri;
            new_cache_state->higher_pri = NULL;
            cache->highest_pri = new_cache_state;
        }
    }

    free(parents_stack);

    var_AUTO(count, cache->count_elements_in_cache);
    const_AUTO(limit, cache->max_num_elements_in_cache);

    while (count > limit)
    {
        fcs_cache_key_info *lowest_pri = cache->lowest_pri;
#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
        int rc_int;
        JLD(rc_int, cache->states_values_to_keys_map,
            (Word_t)(lowest_pri->val_ptr));
#else
        fc_solve_kaz_tree_delete_free(cache->kaz_tree,
            fc_solve_kaz_tree_lookup(cache->kaz_tree, lowest_pri));
#endif

        cache->lowest_pri = lowest_pri->higher_pri;
        cache->lowest_pri->lower_pri = NULL;

        NEXT_CACHE_STATE(lowest_pri) = cache->recycle_bin;

        cache->recycle_bin = lowest_pri;
        --count;
    }

    cache->count_elements_in_cache = count;

    return &(new_cache_state->key);
}

#undef NEXT_CACHE_STATE
#endif

#ifdef DEBUG
#define TRACE0(message)                                                        \
    fcs_trace("BestFS - %s ; Iters=%ld.\n", message,                           \
        (long)(*instance_num_checked_states_ptr))
#else
#define TRACE0(no_use)
#endif

#define my_brfs_queue (BRFS_VAR(soft_thread, bfs_queue))
#define my_brfs_queue_last_item (BRFS_VAR(soft_thread, bfs_queue_last_item))
#define my_brfs_recycle_bin (BRFS_VAR(soft_thread, recycle_bin))

#define NEW_BRFS_QUEUE_ITEM()                                                  \
    ((fcs_states_linked_list_item *)fcs_compact_alloc_ptr(                     \
        &(HT_FIELD(hard_thread, allocator)),                                   \
        sizeof(fcs_states_linked_list_item)));

static inline void fc_solve_initialize_bfs_queue(
    fcs_soft_thread *const soft_thread)
{
    fcs_hard_thread *const hard_thread = soft_thread->hard_thread;

    /* Initialize the BFS queue. We have one dummy element at the beginning
       in order to make operations simpler. */
    my_brfs_queue = NEW_BRFS_QUEUE_ITEM();
    my_brfs_queue_last_item = my_brfs_queue->next = NEW_BRFS_QUEUE_ITEM();
    my_brfs_queue_last_item->next = NULL;
    my_brfs_recycle_bin = NULL;
}

void fc_solve_soft_thread_init_befs_or_bfs(fcs_soft_thread *const soft_thread)
{
#ifdef FCS_WITH_MOVES
    if (soft_thread->is_befs)
    {
#endif
#define WEIGHTING(soft_thread) (&(BEFS_VAR(soft_thread, weighting)))
        /* Initialize the priotity queue of the BeFS scan */
        fc_solve_pq_init(&(BEFS_VAR(soft_thread, pqueue)));
        fc_solve_initialize_befs_rater(soft_thread, WEIGHTING(soft_thread));
#ifdef FCS_WITH_MOVES
    }
    else
    {
        fc_solve_initialize_bfs_queue(soft_thread);
    }
#endif

    if (!BEFS_M_VAR(soft_thread, moves_list))
    {
        size_t num = 0;
        fcs_move_func *moves_list = NULL;

        for (size_t group_idx = 0;
             group_idx < soft_thread->by_depth_moves_order.by_depth_moves[0]
                             .moves_order.num;
             ++group_idx)
        {
            add_to_move_funcs_list(&moves_list, &num,
                soft_thread->by_depth_moves_order.by_depth_moves[0]
                    .moves_order.groups[group_idx]
                    .move_funcs,
                soft_thread->by_depth_moves_order.by_depth_moves[0]
                    .moves_order.groups[group_idx]
                    .num);
        }
        BEFS_M_VAR(soft_thread, moves_list) = moves_list;
        BEFS_M_VAR(soft_thread, moves_list_end) = moves_list + num;
    }
    BEFS_M_VAR(soft_thread, first_state_to_check) =
        FCS_STATE_keyval_pair_to_collectible(
            &fcs_st_instance(soft_thread)->state_copy);
}

/*
 * These functions are used by the move functions in freecell.c and
 * simpsim.c.
 * */
int fc_solve_sfs_check_state_begin(fcs_hard_thread *const hard_thread,
    fcs_kv_state *const out_new_state_out,
    fcs_kv_state raw_state_raw SFS__PASS_MOVE_STACK(
        fcs_move_stack *const moves))
{
    fcs_collectible_state *raw_ptr_new_state;
    fcs_instance *const instance = HT_INSTANCE(hard_thread);

    if ((HT_FIELD(hard_thread, allocated_from_list) =
                (instance->list_of_vacant_states != NULL)))
    {
        raw_ptr_new_state = instance->list_of_vacant_states;
        instance->list_of_vacant_states =
            FCS_S_NEXT(instance->list_of_vacant_states);
    }
    else
    {
        raw_ptr_new_state =
            fcs_state_ia_alloc_into_var(&(HT_FIELD(hard_thread, allocator)));
    }

    FCS_STATE_collectible_to_kv(out_new_state_out, raw_ptr_new_state);
    fcs_duplicate_kv_state(out_new_state_out, &raw_state_raw);
#ifdef FCS_RCS_STATES
#define INFO_STATE_PTR(kv_ptr) ((kv_ptr)->val)
#else
/* TODO : That's very hacky - get rid of it. */
#define INFO_STATE_PTR(kv_ptr) ((fcs_state_keyval_pair *)((kv_ptr)->key))
#endif
    /* Some BeFS and BFS parameters that need to be initialized in
     * the derived state.
     * */
    FCS_S_PARENT(raw_ptr_new_state) = INFO_STATE_PTR(&raw_state_raw);
#ifdef FCS_WITH_MOVES
    FCS_S_MOVES_TO_PARENT(raw_ptr_new_state) = moves;
#endif
/* Make sure depth is consistent with the game graph.
 * I.e: the depth of every newly discovered state is derived from
 * the state from which it was discovered. */
#ifndef FCS_WITHOUT_DEPTH_FIELD
    (FCS_S_DEPTH(raw_ptr_new_state))++;
#endif
    /* Mark this state as a state that was not yet visited */
    FCS_S_VISITED(raw_ptr_new_state) = 0;
    /* It's a newly created state which does not have children yet. */
    FCS_S_NUM_ACTIVE_CHILDREN(raw_ptr_new_state) = 0;
    memset(&(FCS_S_SCAN_VISITED(raw_ptr_new_state)), '\0',
        sizeof(FCS_S_SCAN_VISITED(raw_ptr_new_state)));
    fcs_move_stack_reset(moves);

    return 0;
}

extern fcs_collectible_state *fc_solve_sfs_check_state_end(
    fcs_soft_thread *const soft_thread,
#ifndef FCS_HARD_CODE_REPARENT_STATES_AS_FALSE
    fcs_kv_state raw_state_raw,
#endif
    fcs_kv_state *const raw_ptr_new_state_raw FCS__pass_moves(
        fcs_move_stack *const moves GCC_UNUSED))
{
    const_SLOT(hard_thread, soft_thread);
    const_AUTO(instance, HT_INSTANCE(hard_thread));
#if !defined(FCS_WITHOUT_DEPTH_FIELD) &&                                       \
    !defined(FCS_HARD_CODE_CALC_REAL_DEPTH_AS_FALSE)
    const bool calc_real_depth = fcs_get_calc_real_depth(instance);
#endif
#if !defined(FCS_HARD_CODE_REPARENT_STATES_AS_FALSE) &&                        \
    !defined(FCS_HARD_CODE_SCANS_SYNERGY_AS_TRUE)
    const bool scans_synergy =
        STRUCT_QUERY_FLAG(instance, FCS_RUNTIME_SCANS_SYNERGY);
#endif
    fcs_kv_state existing_state;

#define ptr_new_state_foo (raw_ptr_new_state_raw->val)

    if (!fc_solve_check_and_add_state(
            hard_thread, raw_ptr_new_state_raw, &existing_state))
    {
        if (HT_FIELD(hard_thread, allocated_from_list))
        {
            ptr_new_state_foo->parent = instance->list_of_vacant_states;
            instance->list_of_vacant_states =
                INFO_STATE_PTR(raw_ptr_new_state_raw);
        }
        else
        {
            fcs_compact_alloc_release(&(HT_FIELD(hard_thread, allocator)));
        }

#ifndef FCS_WITHOUT_DEPTH_FIELD
        calculate_real_depth(
            calc_real_depth, FCS_STATE_kv_to_collectible(&existing_state));
#endif

/* Re-parent the existing state to this one.
 *
 * What it means is that if the depth of the state if it
 * can be reached from this one is lower than what it
 * already have, then re-assign its parent to this state.
 * */
#ifndef FCS_HARD_CODE_REPARENT_STATES_AS_FALSE
#define ptr_state (raw_state_raw.val)
        if (STRUCT_QUERY_FLAG(instance, FCS_RUNTIME_TO_REPARENT_STATES_REAL) &&
            (kv_calc_depth(&existing_state) >
                kv_calc_depth(&raw_state_raw) + 1))
        {
#ifdef FCS_WITH_MOVES
            /* Make a copy of "moves" because "moves" will be destroyed */
            existing_state.val->moves_to_parent =
                fc_solve_move_stack_compact_allocate(hard_thread, moves);
#endif
            if (!(existing_state.val->visited & FCS_VISITED_DEAD_END))
            {
                if ((--(FCS_S_NUM_ACTIVE_CHILDREN(
                        existing_state.val->parent))) == 0)
                {
                    MARK_AS_DEAD_END(existing_state.val->parent);
                }
                ptr_state->num_active_children++;
            }
            existing_state.val->parent = INFO_STATE_PTR(&raw_state_raw);
#ifndef FCS_WITHOUT_DEPTH_FIELD
            existing_state.val->depth = ptr_state->depth + 1;
#endif
        }
#endif
        return FCS_STATE_kv_to_collectible(&existing_state);
    }
    else
    {
        return INFO_STATE_PTR(raw_ptr_new_state_raw);
    }
}
