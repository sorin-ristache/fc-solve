#include <stdio.h>
#include "config.h"

#include "inline.h"

#include "kaz_tree.h"
#include "bool.h"

typedef unsigned char fcs_encoded_state_buffer_t[24];

struct fcs_cache_key_info_struct
{
    fcs_encoded_state_buffer_t key;
    /* lower_pri and higher_pri form a doubly linked list.
     *
     * pri == priority.
     * */
    struct fcs_cache_key_info_struct * lower_pri, * higher_pri;
};

typedef struct fcs_cache_key_info_struct fcs_cache_key_info_t;

typedef struct
{
#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
    Pvoid_t states_values_to_keys_map;
#elif (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_KAZ_TREE)
    dict_t * kaz_tree;
#else
#error unknown FCS_RCS_CACHE_STORAGE
#endif
    fcs_compact_allocator_t states_values_to_keys_allocator;
    long count_elements_in_cache, max_num_elements_in_cache;

    fcs_cache_key_info_t * lowest_pri, * highest_pri;

    fcs_cache_key_info_t * recycle_bin;
} fcs_lru_cache_t;

/* TODO: make sure the key is '\0'-padded. */
static int fc_solve_compare_lru_cache_keys(
    const void * void_a, const void * void_b, void * context
)
{
#define GET_PARAM(p) ((((const fcs_cache_key_info_t *)(p))->key))
    return memcmp(GET_PARAM(void_a), GET_PARAM(void_b), sizeof(GET_PARAM(void_a)));
#undef GET_PARAM
}

static void GCC_INLINE cache_init(fcs_lru_cache_t * cache, long max_num_elements_in_cache)
{
#if (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_JUDY)
    cache->states_values_to_keys_map = ((Pvoid_t) NULL);
#elif (FCS_RCS_CACHE_STORAGE == FCS_RCS_CACHE_STORAGE_KAZ_TREE)
    cache->kaz_tree = fc_solve_kaz_tree_create(fc_solve_compare_lru_cache_keys, NULL);
#else
#error Unknown FCS_RCS_CACHE_STORAGE
#endif

    fc_solve_compact_allocator_init(
        &(cache->states_values_to_keys_allocator)
    );
    cache->lowest_pri = NULL;
    cache->highest_pri = NULL;
    cache->recycle_bin = NULL;
    cache->count_elements_in_cache = 0;
    cache->max_num_elements_in_cache = max_num_elements_in_cache;
}

static fcs_bool_t cache_does_key_exist(fcs_lru_cache_t * cache, unsigned char * key)
{
    fcs_cache_key_info_t to_check;
    dnode_t * node;

    memcpy(to_check.key, key, sizeof(to_check.key));

    node = fc_solve_kaz_tree_lookup(cache->kaz_tree, &to_check);

    if (! node)
    {
        return FALSE;
    }
    else
    {
        /* First - promote this key to the top of the cache. */
        fcs_cache_key_info_t * existing;

        existing = (fcs_cache_key_info_t *)(node->dict_key);

        if (existing->higher_pri)
        {
            existing->higher_pri->lower_pri =
                existing->lower_pri;
        }
        if (existing->lower_pri)
        {
            existing->lower_pri->higher_pri =
                existing->higher_pri;
        }
        cache->highest_pri->higher_pri = existing;
        existing->lower_pri = cache->highest_pri;
        existing->higher_pri = NULL;
        cache->highest_pri = existing;

        return TRUE;
    }
}

/* Temporary main() function to make gcc happy. */
int main(int argc, char * argv[])
{
    printf("%s\n", "Hello");

    return 0;
}
