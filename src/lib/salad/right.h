#pragma once

#include "small/matras.h"

static const size_t right_extent_size = 16 * 1024;

namespace {
void *
my_right_alloc()
{
	return malloc(right_extent_size);
}
void
my_right_free(void *p)
{
	free(p);
}
}

struct right_node {
	hash_value_t value;
	hash_t hash;
	hash_t next;
};

struct right {
	hash_t count;
	hash_t cover_mask;
	struct matras mtable;
	arg_t arg;
};

void
right_init(struct right *ht, arg_t a)
{
	ht->count = 0;
	ht->cover_mask = 0;
	matras_create(&ht->mtable, right_extent_size, sizeof(struct right_node),
		      my_right_alloc, my_right_free);
	ht->arg = a;

}

void
right_destroy(struct right *ht)
{
	matras_destroy(&ht->mtable);
}

inline hash_t
right_slot(const struct right *ht, hash_t hash)
{
	assert(ht->count >= ((ht->cover_mask + 1) >> 1) && ht->count <= (ht->cover_mask + 1));
	hash_t mask = ht->cover_mask;
	hash_t res = hash & mask;
	if (res >= ht->count)
		res = hash & (mask >> 1);
	assert(res < ht->count);
	return res;
}

inline hash_value_t
right_get(const struct right *ht, hash_t slot)
{
	assert(slot < ht->count);
	struct right_node *entry = (struct right_node *)
		matras_get(&ht->mtable, slot);
	return entry->value;
}

hash_t
right_find(struct right *ht, hash_t hash, hash_value_t value)
{
	if (ht->count == 0)
		return hash_end;
	hash_t slot = right_slot(ht, hash);
	/*
	if (right_slot(ht, ht->table[slot].hash) != slot)
		return hash_end;
	*/
	do {
		struct right_node *entry = (struct right_node *)
			matras_get(&ht->mtable, slot);
		if (entry->hash == hash && equal(entry->value, value, ht->arg))
			return slot;
		slot = entry->next;
	} while (slot != hash_end);
	return hash_end;
}

hash_t
right_replace(struct right *ht, hash_t hash, hash_value_t value, hash_value_t *old_value)
{
	if (ht->count == 0)
		return hash_end;
	hash_t slot = right_slot(ht, hash);
	/*
	if (right_slot(ht, ht->table[slot].hash) != slot)
		return hash_end;
	*/
	do {
		struct right_node *entry = (struct right_node *)
			matras_get(&ht->mtable, slot);
		if (entry->hash == hash && equal(entry->value, value, ht->arg)) {
			*old_value = entry->value;
			entry->value = value;
			return slot;
		}
		slot = entry->next;
	} while (slot != hash_end);
	return hash_end;
}

hash_t
right_find_key(struct right *ht, hash_t hash, hash_key_t key)
{
	if (ht->count == 0)
		return hash_end;
	hash_t slot = right_slot(ht, hash);
	/*
	if (right_slot(ht, ht->table[slot].hash) != slot)
		return hash_end;
	*/
	do {
		struct right_node *entry = (struct right_node *)
			matras_get(&ht->mtable, slot);
		if (entry->hash == hash && equal_key(entry->value, key, ht->arg))
			return slot;
		slot = entry->next;
	} while (slot != hash_end);
	return hash_end;
}

hash_t
right_insert(struct right *ht, hash_t hash, hash_value_t value)
{
	if (ht->count == 0) {
		ht->count = 1;
		assert(ht->cover_mask == 0);
		uint32_t id;
		struct right_node *entry = (struct right_node *)
			matras_alloc(&ht->mtable, &id);
		assert(id == 0);
		entry->value = value;
		entry->hash = hash;
		entry->next = hash_end;
		return (hash_t)0;
	}

	assert(ht->cover_mask + 1 >= ht->count);
	if (ht->cover_mask + 1 == ht->count)
		ht->cover_mask = (ht->cover_mask << 1) | (hash_t)1;
	hash_t empty_slot = ht->count++;
	uint32_t id;
	struct right_node *empty = (struct right_node *)
		matras_alloc(&ht->mtable, &id);
	assert(id == empty_slot);
	assert(ht->count >= 2);
	assert(right_slot(ht, empty_slot) == empty_slot);

	hash_t split_comm_mask = ht->cover_mask >> 1;
	hash_t susp_slot = empty_slot & split_comm_mask;
	assert(right_slot(ht, susp_slot) == susp_slot);
	struct right_node *susp = (struct right_node *)
		matras_get(&ht->mtable, susp_slot);

	if ((susp->hash & split_comm_mask) == susp_slot) {
		assert(right_slot(ht, susp->hash) == susp_slot || right_slot(ht, susp->hash) == empty_slot);
		hash_t split_diff_mask = ht->cover_mask ^ split_comm_mask;

		struct right_node *chain0_tail = 0;
		struct right_node *chain1_tail = 0;
		struct right_node *split_head = 0;
		hash_t split_head_slot;
		if (susp->hash & split_diff_mask) {
			assert(right_slot(ht, susp->hash) == empty_slot);
			*empty = *susp;
			chain1_tail = empty;
			empty_slot = susp_slot;
			empty = susp;
			while (chain1_tail->next != hash_end) {
				hash_t next_slot = chain1_tail->next;
				struct right_node *next = (struct right_node *)
					matras_get(&ht->mtable, next_slot);
				if (!(next->hash & split_diff_mask)) {
					chain1_tail->next = hash_end;
					chain0_tail = empty;
					*chain0_tail = *next;
					chain0_tail->next = hash_end;
					empty_slot = next_slot;
					empty = next;
					if (next->next != hash_end) {
						split_head_slot = next->next;
						split_head = (struct right_node *)
							matras_get(&ht->mtable, split_head_slot);
					}
					break;
				}
				chain1_tail = next;
			}
		} else {
			assert(right_slot(ht, susp->hash) == susp_slot);
			chain0_tail = susp;
			while (chain0_tail->next != hash_end) {
				hash_t next_slot = chain0_tail->next;
				struct right_node *next = (struct right_node *)
					matras_get(&ht->mtable, next_slot);
				if (next->hash & split_diff_mask) {
					chain0_tail->next = hash_end;
					chain1_tail = empty;
					*chain1_tail = *next;
					chain1_tail->next = hash_end;
					empty_slot = next_slot;
					empty = next;
					if (next->next != hash_end) {
						split_head_slot = next->next;
						split_head = (struct right_node *)
							matras_get(&ht->mtable, split_head_slot);
					}
					break;
				}
				chain0_tail = next;
			}
		}
		while (split_head) {
			assert(chain0_tail);
			assert(chain1_tail);
			if (split_head->hash & split_diff_mask) {
				chain1_tail->next = split_head_slot;
				chain1_tail = split_head;
			} else {
				chain0_tail->next = split_head_slot;
				chain0_tail = split_head;
			}
			if (split_head->next == hash_end)
				break;
			split_head_slot = split_head->next;
			split_head = (struct right_node *)
				matras_get(&ht->mtable, split_head_slot);
		}
		if (chain0_tail)
			chain0_tail->next = hash_end;
		if (chain1_tail)
			chain1_tail->next = hash_end;
	} else {
		assert(right_slot(ht, susp->hash) != susp_slot && right_slot(ht, susp->hash) != empty_slot);
	}

	hash_t slot = right_slot(ht, hash);
	if (slot != empty_slot) {
		struct right_node *s = (struct right_node *)
			matras_get(&ht->mtable, slot);
		hash_t chain_slot = right_slot(ht, s->hash);
		if (chain_slot == slot) {
			empty->value = value;
			empty->hash = hash;
			empty->next = s->next;
			s->next = empty_slot;
			return empty_slot;
		} else {
			struct right_node *chain = (struct right_node *)
				matras_get(&ht->mtable, chain_slot);
			while (chain->next != slot) {
				chain_slot = chain->next;
				chain = (struct right_node *)
					matras_get(&ht->mtable, chain_slot);
			}
			*empty = *s;
			chain->next = empty_slot;
			s->value = value;
			s->hash = hash;
			s->next = hash_end;
			return slot;
		}
	} else {
		empty->value = value;
		empty->hash = hash;
		empty->next = hash_end;
		return empty_slot;
	}

}

void
right_delete(struct right *ht, hash_t slot)
{
	assert(slot < ht->count);
	hash_t empty_slot = slot;
	struct right_node *empty = (struct right_node *)
		matras_get(&ht->mtable, empty_slot);
	hash_t chain_slot = right_slot(ht, empty->hash);
	if (chain_slot == empty_slot) {
		if (empty->next != hash_end) { /* <---------- */
			hash_t tmp_slot = empty->next;
			struct right_node *tmp = (struct right_node *)
				matras_get(&ht->mtable, tmp_slot);
			*empty = *tmp;
			empty_slot = tmp_slot;
			empty = tmp;
		}
	} else {
		struct right_node *chain = (struct right_node *)
			matras_get(&ht->mtable, chain_slot);
		hash_t tmp_slot = chain->next;
		while (tmp_slot != empty_slot) {
			chain_slot = tmp_slot;
			chain = (struct right_node *)
				matras_get(&ht->mtable, tmp_slot);
			tmp_slot = chain->next;
		}
		chain->next = empty->next;
	}
	struct right_node *last = (struct right_node *)
		matras_get(&ht->mtable, ht->count - 1);
	hash_t last_chain_slot = right_slot(ht, last->hash);
	ht->count--;
	if (ht->count == 0) {
		matras_dealloc(&ht->mtable);
		return;
	}
	if (((ht->cover_mask + 1) >> 1) == ht->count)
		ht->cover_mask >>= 1;
	if (empty_slot == ht->count) {
		matras_dealloc(&ht->mtable);
		return;
	}

	*empty = *last;
	if (last_chain_slot == ht->count) {
		hash_t slot = right_slot(ht, last->hash);
		struct right_node *s = (struct right_node *)
			matras_get(&ht->mtable, slot);
		if (slot != empty_slot) {
			chain_slot = right_slot(ht, s->hash);
			if (slot == chain_slot) {
				bool same_chain = false;
				chain_slot = ht->count;
				struct right_node *chain = (struct right_node *)
					matras_get(&ht->mtable, chain_slot);
				hash_t tmp = chain->next;
				while (tmp != hash_end) {
					if (tmp == slot) {
						same_chain = true;
						break;
					}
					chain_slot = tmp;
					chain = (struct right_node *)
						matras_get(&ht->mtable, chain_slot);
					tmp = chain->next;
				}
				if (same_chain) {
					*empty = *s;
					chain->next = empty_slot;
					*s = *last;
				} else {
					tmp = s->next;
					while (tmp != hash_end) {
						slot = tmp;
						s = (struct right_node *)
							matras_get(&ht->mtable, slot);
						tmp = s->next;
					}
					s->next = empty_slot;
					hash_t tmp1_slot = empty_slot;
					struct right_node *tmp1 = (struct right_node *)
						matras_get(&ht->mtable, tmp1_slot);
					hash_t tmp2_slot = tmp1->next;
					while (tmp2_slot != hash_end) {
						if (tmp2_slot == slot) {
							tmp1->next = hash_end;
							break;
						}
						tmp1_slot = tmp2_slot;
						tmp1 = (struct right_node *)
							matras_get(&ht->mtable, tmp1_slot);
						tmp2_slot = tmp1->next;
					}
				}
			} else {
				struct right_node *chain = (struct right_node *)
					matras_get(&ht->mtable, chain_slot);
				*empty = *s;
				hash_t tmp = chain->next;
				while (tmp != slot) {
					chain_slot = tmp;
					chain = (struct right_node *)
						matras_get(&ht->mtable, chain_slot);
					tmp = chain->next;
				}
				chain->next = empty_slot;
				*s = *last;
			}
		}
	} else {
		hash_t slot = last_chain_slot;
		struct right_node *s = (struct right_node *)
			matras_get(&ht->mtable, slot);
		hash_t tmp = s->next;
		while (tmp != ht->count) {
			assert(tmp != hash_end);
			assert(tmp < ht->count);
			slot = tmp;
			s = (struct right_node *)
				matras_get(&ht->mtable, slot);
			tmp = s->next;
		}
		s->next = empty_slot;
	}
	matras_dealloc(&ht->mtable);
}

int
right_selfcheck(const struct right *ht)
{
	int res = 0;
	if (ht->count != ht->mtable.block_count)
		res |= 64;
	for (hash_t i = 0; i < ht->count; i++) {
		struct right_node *n = (struct right_node *)
			matras_get(&ht->mtable, i);
		hash_t slot = right_slot(ht, n->hash);
		if (slot != i) {
			bool found = false;
			hash_t chain_start = slot;
			do {
				struct right_node *s = (struct right_node *)
					matras_get(&ht->mtable, slot);
				slot = s->next;
				if (slot >= ht->count) {
					res |= 16; /* out of bounds (1) */
					break;
				}
				if (slot == i) {
					found = true;
					break;
				}
				if (slot == chain_start) {
					res |= 4; /* cycles in chain (1) */
					break;
				}
			} while (slot != hash_end);
			if (!found)
				res |= 1; /* slot is out of chain */
		} else {
			do {
				struct right_node *s = (struct right_node *)
					matras_get(&ht->mtable, slot);
				if (right_slot(ht, s->hash) != i)
					res |= 2; /* wrong value in chain */
				slot = s->next;
				if (slot != hash_end && slot >= ht->count) {
					res |= 32; /* out of bounds (2) */
					break;
				}
				if (slot == i) {
					res |= 8; /* cycles in chain (2) */
					break;
				}
			} while (slot != hash_end);
		}
	}
	return res;
}

hash_t
right_longest_chain_length(const struct right *ht)
{
	hash_t res = 0;
	for (hash_t i = 0; i < ht->count; i++) {
		struct right_node *n = (struct right_node *)
			matras_get(&ht->mtable, i);
		if (right_slot(ht, n->hash) != i)
			continue;
		hash_t test = 0;
		hash_t slot = i;
		do {
			struct right_node *s = (struct right_node *)
				matras_get(&ht->mtable, slot);
			test++;
			slot = s->next;
		} while (slot != hash_end);
		if (test > res)
			res = test;
	}
	return res;
}

void
right_chain_length_spectre(const struct right *ht, hash_t *spectre, hash_t len)
{
	for (hash_t i = 0; i < len; i++)
		spectre[i] = 0;
	for (hash_t i = 0; i < ht->count; i++) {
		struct right_node *n = (struct right_node *)
			matras_get(&ht->mtable, i);
		if (right_slot(ht, n->hash) != i)
			continue;
		hash_t test = 0;
		hash_t slot = i;
		do {
			struct right_node *s = (struct right_node *)
				matras_get(&ht->mtable, slot);
			test++;
			slot = s->next;
		} while (slot != hash_end);
		if (test >= len)
			test = len - 1;
		spectre[test]++;
	}
}

double
right_average_chain_length(const struct right *ht)
{
	hash_t chain_cnt = 0;
	for (hash_t i = 0; i < ht->count; i++) {
		struct right_node *n = (struct right_node *)
			matras_get(&ht->mtable, i);
		if (right_slot(ht, n->hash) != i)
			continue;
		chain_cnt++;
	}
	return ((double)ht->count) / ((double)chain_cnt);
}

size_t
right_memsize(const struct right *ht)
{
	return matras_extents_count(&ht->mtable) * right_extent_size;
}
