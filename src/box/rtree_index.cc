/*
 * Redistribution and use in source and binary forms, with or
 * without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above
 *    copyright notice, this list of conditions and the
 *    following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above
 *    copyright notice, this list of conditions and the following
 *    disclaimer in the documentation and/or other materials
 *    provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY <COPYRIGHT HOLDER> ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
 * <COPYRIGHT HOLDER> OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,
 * INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
 * SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR
 * BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
 * THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
#include "rtree_index.h"
#include "tuple.h"
#include "space.h"
#include "exception.h"
#include "errinj.h"
#include "fiber.h"
#include "small/small.h"

/** For all memory used by all rtree indexes. */
static struct mempool rtree_page_pool;
/** Number of allocated pages. */
static int rtree_page_pool_initialized = 0;

/* {{{ Utilities. *************************************************/

inline void extract_rectangle(struct rtree_rect *rect,
			      const struct tuple *tuple, struct key_def *kd)
{
        assert(kd->part_count == 1);
	const char *elems = tuple_field(tuple, kd->parts[0].fieldno);
	uint32_t size = mp_decode_array(&elems);
	switch (size) {
	case 1: // array
	{
		const char* elems = tuple_field(tuple, kd->parts[0].fieldno);
		uint32_t size = mp_decode_array(&elems);
		switch (size) {
		case 2: // point
			rect->lower_point.coords[0] =
				rect->upper_point.coords[0] =
				mp_decode_num(&elems, 0);
			rect->lower_point.coords[1] =
				rect->upper_point.coords[1] =
				mp_decode_num(&elems, 1);
			break;
		case 4:
			rect->lower_point.coords[0] = mp_decode_num(&elems, 0);
			rect->lower_point.coords[1] = mp_decode_num(&elems, 1);
			rect->upper_point.coords[0] = mp_decode_num(&elems, 2);
			rect->upper_point.coords[1] = mp_decode_num(&elems, 3);
			break;
		default:
			tnt_raise(ClientError, ER_UNSUPPORTED,
				  "R-Tree index", "Field should be array with "
				  "size 2 (point) or 4 (rectangle)");

		}
		break;
	}
	case 2: // point
		rect->lower_point.coords[0] =
			rect->upper_point.coords[0] =
			mp_decode_num(&elems, 0);
		rect->lower_point.coords[1] =
			rect->upper_point.coords[1] =
			mp_decode_num(&elems, 1);
		break;
	case 4:
		rect->lower_point.coords[0] = mp_decode_num(&elems, 0);
		rect->lower_point.coords[1] = mp_decode_num(&elems, 1);
		rect->upper_point.coords[0] = mp_decode_num(&elems, 2);
		rect->upper_point.coords[1] = mp_decode_num(&elems, 3);
		break;
	default:
		tnt_raise(ClientError, ER_UNSUPPORTED,
			  "R-Tree index", "Key should contain 2 (point) or 4 (rectangle) coordinates");

	}
	rtree_rect_normalize(rect);
}
/* {{{ TreeIndex Iterators ****************************************/

struct index_rtree_iterator {
        struct iterator base;
        struct rtree_iterator impl;
};

static void
index_rtree_iterator_free(struct iterator *i)
{
	struct index_rtree_iterator *itr = (struct index_rtree_iterator *)i;
	rtree_iterator_destroy(&itr->impl);
        delete itr;
}

static struct tuple *
index_rtree_iterator_next(struct iterator *i)
{
	struct index_rtree_iterator *itr = (struct index_rtree_iterator *)i;
	return (struct tuple *)rtree_iterator_next(&itr->impl);
}

/* }}} */

/* {{{ TreeIndex  **********************************************************/

static void *
rtree_page_alloc()
{
	ERROR_INJECT(ERRINJ_INDEX_ALLOC, return 0);
	return mempool_alloc(&rtree_page_pool);
}

static void
rtree_page_free(void *page)
{
	return mempool_free(&rtree_page_pool, page);
}
RTreeIndex::~RTreeIndex()
{
	// Iterator has to be destroye prior to tree
	if (m_position != NULL) {
		index_rtree_iterator_free(m_position);
		m_position = NULL;
	}
	rtree_destroy(&tree);
}

RTreeIndex::RTreeIndex(struct key_def *key_def)
  : Index(key_def)
{
	assert(key_def->part_count == 1);
	assert(key_def->parts[0].type = ARRAY);
	assert(key_def->is_unique == false);

	if (rtree_page_pool_initialized == 0) {
		mempool_create(&rtree_page_pool, &cord()->slabc,
			       RTREE_PAGE_SIZE);
		rtree_page_pool_initialized = 1;
	}
	rtree_init(&tree, rtree_page_alloc, rtree_page_free);
}

size_t
RTreeIndex::size() const
{
	return rtree_number_of_records(&tree);
}

size_t
RTreeIndex::memsize() const
{
        return rtree_used_size(&tree);
}

struct tuple *
RTreeIndex::findByKey(const char *key, uint32_t part_count) const
{
	rtree_rect rect;
        struct rtree_iterator iterator;
        rtree_iterator_init(&iterator);
        switch (part_count) {
	case 1:
	{
		uint32_t size = mp_decode_array(&key);
		switch (size) {
		case 2:
			rect.lower_point.coords[0] =
				rect.upper_point.coords[0] =
				mp_decode_num(&key, 0);
			rect.lower_point.coords[1] =
				rect.upper_point.coords[1] =
				mp_decode_num(&key, 1);
			break;
		case 4:
			rect.lower_point.coords[0] = mp_decode_num(&key, 0);
			rect.lower_point.coords[1] = mp_decode_num(&key, 1);
			rect.upper_point.coords[0] = mp_decode_num(&key, 2);
			rect.upper_point.coords[1] = mp_decode_num(&key, 3);
			break;
		default:
			assert(false);
		}
		break;
	}
	case 2:
		rect.lower_point.coords[0] =
			rect.upper_point.coords[0] =
			mp_decode_num(&key, 0);
		rect.lower_point.coords[1] =
			rect.upper_point.coords[1] =
			mp_decode_num(&key, 1);
		break;
	case 4:
		rect.lower_point.coords[0] = mp_decode_num(&key, 0);
		rect.lower_point.coords[1] = mp_decode_num(&key, 1);
		rect.upper_point.coords[0] = mp_decode_num(&key, 2);
		rect.upper_point.coords[1] = mp_decode_num(&key, 3);
		break;
	default:
		assert(false);
	}
        struct tuple *result = NULL;
        if (rtree_search(&tree, &rect, SOP_OVERLAPS, &iterator))
        	result = (struct tuple *)rtree_iterator_next(&iterator);
        rtree_iterator_destroy(&iterator);
        return result;
}

struct tuple *
RTreeIndex::replace(struct tuple *old_tuple, struct tuple *new_tuple,
                    enum dup_replace_mode)
{
        struct rtree_rect rect;
        if (new_tuple) {
                extract_rectangle(&rect, new_tuple, key_def);
                rtree_insert(&tree, &rect, new_tuple);
        }
	if (old_tuple) {
                extract_rectangle(&rect, old_tuple, key_def);
                if (!rtree_remove(&tree, &rect, old_tuple))
                        old_tuple = NULL;
        }
        return old_tuple;
}

struct iterator *
RTreeIndex::allocIterator() const
{
	index_rtree_iterator *it = new index_rtree_iterator;
	memset(it, 0, sizeof(*it));
	rtree_iterator_init(&it->impl);
	if (it == NULL) {
		tnt_raise(ClientError, ER_MEMORY_ISSUE,
			  sizeof(struct index_rtree_iterator),
			  "RTreeIndex", "iterator");
	}
	it->base.next = index_rtree_iterator_next;
	it->base.free = index_rtree_iterator_free;
	return &it->base;
}

void
RTreeIndex::initIterator(struct iterator *iterator, enum iterator_type type,
                         const char *key, uint32_t part_count) const
{
        struct rtree_rect rect;
        index_rtree_iterator *it = (index_rtree_iterator *)iterator;
        switch (part_count) {
        case 0:
                if (type != ITER_ALL) {
                        tnt_raise(ClientError, ER_UNSUPPORTED,
				  "R-Tree index", "It is possible to omit key only for ITER_ALL");
                }
                break;
	case 1:
	{
		uint32_t size = mp_decode_array(&key);
		switch (size) {
		case 2:
			rect.lower_point.coords[0] =
				rect.upper_point.coords[0] =
				mp_decode_num(&key, 0);
			rect.lower_point.coords[1] =
				rect.upper_point.coords[1] =
				mp_decode_num(&key, 1);
			break;
		case 4:
			rect.lower_point.coords[0] = mp_decode_num(&key, 0);
			rect.lower_point.coords[1] = mp_decode_num(&key, 1);
			rect.upper_point.coords[0] = mp_decode_num(&key, 2);
			rect.upper_point.coords[1] = mp_decode_num(&key, 3);
			break;
		default:
			tnt_raise(ClientError, ER_UNSUPPORTED,
				  "R-Tree index", "Key should be array of 2 (point) "
				  "or 4 (rectangle) numeric coordinates");
		}
		break;
	}
	case 2:
		rect.lower_point.coords[0] =
			rect.upper_point.coords[0] =
			mp_decode_num(&key, 0);
		rect.lower_point.coords[1] =
			rect.upper_point.coords[1] =
			mp_decode_num(&key, 1);
		break;
	case 4:
		rect.lower_point.coords[0] = mp_decode_num(&key, 0);
		rect.lower_point.coords[1] = mp_decode_num(&key, 1);
		rect.upper_point.coords[0] = mp_decode_num(&key, 2);
		rect.upper_point.coords[1] = mp_decode_num(&key, 3);
		break;
	default:
		tnt_raise(ClientError, ER_UNSUPPORTED,
			  "R-Tree index", "Key contain 2 (point) "
			  "or 4 (rectangle) numeric coordinates");
	}
        spatial_search_op op;
        switch (type) {
        case ITER_ALL:
                op = SOP_ALL;
                break;
        case ITER_EQ:
                op = SOP_EQUALS;
                break;
        case ITER_GT:
                op = SOP_STRICT_CONTAINS;
                break;
        case ITER_GE:
                op = SOP_CONTAINS;
                break;
        case ITER_LT:
                op = SOP_STRICT_BELONGS;
                break;
        case ITER_LE:
                op = SOP_BELONGS;
                break;
        case ITER_OVERLAPS:
                op = SOP_OVERLAPS;
                break;
        case ITER_NEIGHBOR:
                op = SOP_NEIGHBOR;
                break;
        default:
                tnt_raise(ClientError, ER_UNSUPPORTED,
                          "R-Tree index", "Unsupported search operation for R-Tree");
        }
        rtree_search(&tree, &rect, op, &it->impl);
}

void
RTreeIndex::beginBuild()
{
	rtree_purge(&tree);
}


