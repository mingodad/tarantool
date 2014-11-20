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
#include "hash_index.h"
#include "say.h"
#include "tuple.h"
#include "exception.h"
#include "errinj.h"

#include "third_party/PMurHash.h"

enum {
	HASH_SEED = 13U
};

static inline bool
equal(struct tuple *tuple_a, struct tuple *tuple_b,
	    const struct key_def *key_def)
{
	return tuple_compare(tuple_a, tuple_b, key_def) == 0;
}

static inline bool
equal_key(struct tuple *tuple, const char *key,
		const struct key_def *key_def)
{
	return tuple_compare_with_key(tuple, key, key_def->part_count,
				      key_def) == 0;
}

static inline uint32_t
mh_hash_field(uint32_t *ph1, uint32_t *pcarry, const char **field,
	      enum field_type type)
{
	const char *f = *field;
	uint32_t size;

	switch (type) {
	case STRING:
		/*
		 * (!) MP_STR fields hashed **excluding** MsgPack format
		 * indentifier. We have to do that to keep compatibility
		 * with old third-party MsgPack (spec-old.md) implementations.
		 * \sa https://github.com/tarantool/tarantool/issues/522
		 */
		f = mp_decode_str(field, &size);
		break;
	default:
		mp_next(field);
		size = *field - f;  /* calculate the size of field */
		/*
		 * (!) All other fields hashed **including** MsgPack format
		 * identifier (e.g. 0xcc). This was done **intentionally**
		 * for performance reasons. Please follow MsgPack specification
		 * and pack all your numbers to the most compact representation.
		 * If you still want to add support for broken MsgPack,
		 * please don't forget to patch tuple_compare_field().
		 */
		break;
	}
	assert(size < INT32_MAX);
	PMurHash32_Process(ph1, pcarry, f, size);
	return size;
}

static inline uint32_t
tuple_hash(struct tuple *tuple, const struct key_def *key_def)
{
	const struct key_part *part = key_def->parts;
	/*
	 * Speed up the simplest case when we have a
	 * single-part hash over an integer field.
	 */
	if (key_def->part_count == 1 && part->type == NUM) {
		const char *field = tuple_field(tuple, part->fieldno);
		uint64_t val = mp_decode_uint(&field);
		if (likely(val <= UINT32_MAX))
			return val;
		return ((uint32_t)((val)>>33^(val)^(val)<<11));
	}

	uint32_t h = HASH_SEED;
	uint32_t carry = 0;
	uint32_t total_size = 0;

	for ( ; part < key_def->parts + key_def->part_count; part++) {
		const char *field = tuple_field(tuple, part->fieldno);
		total_size += mh_hash_field(&h, &carry, &field, part->type);
	}

	return PMurHash32_Result(h, carry, total_size);
}

static inline uint32_t
key_hash(const char *key, const struct key_def *key_def)
{
	const struct key_part *part = key_def->parts;

	if (key_def->part_count == 1 && part->type == NUM) {
		uint64_t val = mp_decode_uint(&key);
		if (likely(val <= UINT32_MAX))
			return val;
		return ((uint32_t)((val)>>33^(val)^(val)<<11));
	}

	uint32_t h = HASH_SEED;
	uint32_t carry = 0;
	uint32_t total_size = 0;

	/* Hash fields part by part (see mh_hash_field() comments) */
	for ( ; part < key_def->parts + key_def->part_count; part++)
		total_size += mh_hash_field(&h, &carry, &key, part->type);

	return PMurHash32_Result(h, carry, total_size);
}

typedef struct tuple *hash_value_t;
typedef const char *hash_key_t;
typedef struct key_def *arg_t;
typedef uint32_t hash_t;
static const hash_t hash_end = (hash_t)-1;
#include "salad/right.h"

/* {{{ HashIndex Iterators ****************************************/

struct hash_iterator {
	struct iterator base; /* Must be the first member. */
	struct right *hash;
	uint32_t h_pos;
};

void
hash_iterator_free(struct iterator *iterator)
{
	assert(iterator->free == hash_iterator_free);
	free(iterator);
}

struct tuple *
hash_iterator_ge(struct iterator *ptr)
{
	assert(ptr->free == hash_iterator_free);
	struct hash_iterator *it = (struct hash_iterator *) ptr;

	if (it->h_pos < it->hash->count)
		return right_get(it->hash, it->h_pos++);
	return NULL;
}

static struct tuple *
hash_iterator_eq_next(struct iterator *it __attribute__((unused)))
{
	return NULL;
}

static struct tuple *
hash_iterator_eq(struct iterator *it)
{
	it->next = hash_iterator_eq_next;
	return hash_iterator_ge(it);
}

/* }}} */

/* {{{ HashIndex -- implementation of all hashes. **********************/

HashIndex::HashIndex(struct key_def *key_def)
	: Index(key_def)
{
	hash = new struct right;
	if (hash == NULL) {
		tnt_raise(ClientError, ER_MEMORY_ISSUE, sizeof(hash),
			  "HashIndex", "hash");
	}
	right_init(hash, this->key_def);
}

HashIndex::~HashIndex()
{
	right_destroy(hash);
	delete hash;
}

void
HashIndex::reserve(uint32_t size_hint)
{
	(void)size_hint;
}

size_t
HashIndex::size() const
{
	return hash->count;
}

size_t
HashIndex::memsize() const
{
        return right_memsize(hash);
}

struct tuple *
HashIndex::random(uint32_t rnd) const
{
	if (hash->count == 0)
		return NULL;
	return right_get(hash, rnd % hash->count);
}

struct tuple *
HashIndex::findByKey(const char *key, uint32_t part_count) const
{
	assert(key_def->is_unique && part_count == key_def->part_count);
	(void) part_count;

	struct tuple *ret = NULL;
	uint32_t h = key_hash(key, key_def);
	uint32_t k = right_find_key(hash, h, key);
	if (k != hash_end)
		ret = right_get(hash, k);
	return ret;
}

struct tuple *
HashIndex::replace(struct tuple *old_tuple, struct tuple *new_tuple,
		   enum dup_replace_mode mode)
{
	uint32_t errcode;

	if (new_tuple) {
		uint32_t h = tuple_hash(new_tuple, key_def);
		struct tuple *dup_tuple = NULL;
		hash_t pos = right_replace(hash, h, new_tuple, &dup_tuple);
		if (pos == hash_end)
			pos = right_insert(hash, h, new_tuple);

		ERROR_INJECT(ERRINJ_INDEX_ALLOC,
		{
			right_delete(hash, pos);
			pos = hash_end;
		});

		if (pos == hash_end) {
			tnt_raise(LoggedError, ER_MEMORY_ISSUE, (ssize_t) hash->count,
				  "hash", "key");
		}
		errcode = replace_check_dup(old_tuple, dup_tuple, mode);

		if (errcode) {
			right_delete(hash, pos);
			if (dup_tuple) {
				uint32_t pos = right_insert(hash, h, dup_tuple);
				if (pos == hash_end) {
					panic("Failed to allocate memory in "
					      "recover of int hash");
				}
			}
			tnt_raise(ClientError, errcode, index_id(this));
		}

		if (dup_tuple)
			return dup_tuple;
	}

	if (old_tuple) {
		uint32_t h = tuple_hash(old_tuple, key_def);
		hash_t slot = right_find(hash, h, old_tuple);
		if (slot != hash_end)
			right_delete(hash, slot);
	}
	return old_tuple;
}

struct iterator *
HashIndex::allocIterator() const
{
	struct hash_iterator *it = (struct hash_iterator *)
			calloc(1, sizeof(*it));
	if (it == NULL) {
		tnt_raise(ClientError, ER_MEMORY_ISSUE,
			  sizeof(struct hash_iterator),
			  "HashIndex", "iterator");
	}

	it->base.next = hash_iterator_ge;
	it->base.free = hash_iterator_free;
	return (struct iterator *) it;
}

void
HashIndex::initIterator(struct iterator *ptr, enum iterator_type type,
			const char *key, uint32_t part_count) const
{
	assert(part_count == 0 || key != NULL);
	(void) part_count;
	assert(ptr->free == hash_iterator_free);

	struct hash_iterator *it = (struct hash_iterator *) ptr;

	switch (type) {
	case ITER_ALL:
		it->h_pos = 0;
		it->base.next = hash_iterator_ge;
		break;
	case ITER_EQ:
		assert(part_count > 0);
		it->h_pos = right_find_key(hash, key_hash(key, key_def), key);
		it->base.next = hash_iterator_eq;
		break;
	default:
		tnt_raise(ClientError, ER_UNSUPPORTED,
			  "Hash index", "requested iterator type");
	}
	it->hash = hash;
}
/* }}} */
