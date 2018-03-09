/*-
 * Copyright 2013-2018 Alexander Peslyak
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <sys/mman.h>

#define HUGEPAGE_THRESHOLD		(32 * 1024 * 1024)

#ifdef __x86_64__
#define HUGEPAGE_SIZE			(2 * 1024 * 1024)
#else
#undef HUGEPAGE_SIZE
#endif

static void *alloc_region(yescrypt_region_t *region, size_t size)
{
	size_t base_size = size;
	uint8_t *base, *aligned;
#ifdef MAP_ANON
	int flags =
#ifdef MAP_NOCORE
	    MAP_NOCORE |
#endif
#ifdef MAP_POPULATE
	    MAP_POPULATE |
#endif
	    MAP_ANON | MAP_PRIVATE;
#if defined(MAP_HUGETLB) && defined(HUGEPAGE_SIZE)
	size_t new_size = size;
	const size_t hugepage_mask = (size_t)HUGEPAGE_SIZE - 1;
	if (size >= HUGEPAGE_THRESHOLD && size + hugepage_mask >= size) {
		flags |= MAP_HUGETLB;
/*
 * Linux's munmap() fails on MAP_HUGETLB mappings if size is not a multiple of
 * huge page size, so let's round up to huge page size here.
 */
		new_size = size + hugepage_mask;
		new_size &= ~hugepage_mask;
	}
	base = mmap(NULL, new_size, PROT_READ | PROT_WRITE, flags, -1, 0);
	if (base != MAP_FAILED) {
		base_size = new_size;
	} else if (flags & MAP_HUGETLB) {
		flags &= ~MAP_HUGETLB;
		base = mmap(NULL, size, PROT_READ | PROT_WRITE, flags, -1, 0);
	}

#else
	base = mmap(NULL, size, PROT_READ | PROT_WRITE, flags, -1, 0);
#endif
	if (base == MAP_FAILED)
		base = NULL;
	aligned = base;
#elif defined(HAVE_POSIX_MEMALIGN)
	if ((errno = posix_memalign((void **)&base, 64, size)) != 0)
		base = NULL;
	aligned = base;
#else
	base = aligned = NULL;
	if (size + 63 < size) {
		errno = ENOMEM;
	} else if ((base = malloc(size + 63)) != NULL) {
		aligned = base + 63;
		aligned -= (uintptr_t)aligned & 63;
	}
#endif
	region->base = base;
	region->aligned = aligned;
	region->base_size = base ? base_size : 0;
	region->aligned_size = base ? size : 0;
	return aligned;
}

static inline void init_region(yescrypt_region_t *region)
{
	region->base = region->aligned = NULL;
	region->base_size = region->aligned_size = 0;
}

static int free_region(yescrypt_region_t *region)
{
	if (region->base) {
#ifdef MAP_ANON
		if (munmap(region->base, region->base_size))
			return -1;
#else
		free(region->base);
#endif
	}
	init_region(region);
	return 0;
}

int yescrypt_init_shared(yescrypt_shared_t *shared,
    const uint8_t *seed, size_t seedlen, const yescrypt_params_t *params)
{
	yescrypt_params_t subparams;
	yescrypt_shared_t half1, half2;
	uint8_t salt[32];
	uint64_t *tag;

	subparams = *params;
	subparams.flags |= YESCRYPT_INIT_SHARED;
	subparams.N = params->NROM;
	subparams.NROM = 0;

	if (!(params->flags & YESCRYPT_RW) || params->N || params->g)
		return -1;

	if (params->flags & YESCRYPT_SHARED_PREALLOCATED) {
		if (!shared->aligned || !shared->aligned_size)
			return -1;

/* Overwrite a possible old ROM tag before we overwrite the rest */
		tag = (uint64_t *)
		    ((uint8_t *)shared->aligned + shared->aligned_size - 48);
		memset(tag, 0, 48);
	} else {
		init_region(shared);

		subparams.flags |= YESCRYPT_ALLOC_ONLY;
		if (yescrypt_kdf(NULL, shared, NULL, 0, NULL, 0, &subparams,
		    NULL, 0) != -2 || !shared->aligned)
			return -1;
		subparams.flags -= YESCRYPT_ALLOC_ONLY;
	}

	subparams.N /= 2;

	half1 = *shared;
	half1.aligned_size /= 2;
	half2 = half1;
	half2.aligned += half1.aligned_size;

	if (yescrypt_kdf(NULL, &half1,
	    seed, seedlen, (uint8_t *)"yescrypt-ROMhash", 16, &subparams,
	    salt, sizeof(salt)))
		goto fail;

	subparams.NROM = subparams.N;

	if (yescrypt_kdf(&half1, &half2,
	    seed, seedlen, salt, sizeof(salt), &subparams, salt, sizeof(salt)))
		goto fail;

	if (yescrypt_kdf(&half2, &half1,
	    seed, seedlen, salt, sizeof(salt), &subparams, salt, sizeof(salt)))
		goto fail;

	tag = (uint64_t *)
	    ((uint8_t *)shared->aligned + shared->aligned_size - 48);
	tag[0] = YESCRYPT_ROM_TAG1;
	tag[1] = YESCRYPT_ROM_TAG2;
	tag[2] = le64dec(salt);
	tag[3] = le64dec(salt + 8);
	tag[4] = le64dec(salt + 16);
	tag[5] = le64dec(salt + 24);

	insecure_memzero(salt, sizeof(salt));
	return 0;

fail:
	insecure_memzero(salt, sizeof(salt));
	if (!(params->flags & YESCRYPT_SHARED_PREALLOCATED))
		free_region(shared);
	return -1;
}

yescrypt_binary_t *yescrypt_digest_shared(yescrypt_shared_t *shared)
{
	static yescrypt_binary_t digest;
	uint64_t *tag;

	if (shared->aligned_size < 48)
		return NULL;

	tag = (uint64_t *)
	    ((uint8_t *)shared->aligned + shared->aligned_size - 48);

	if (tag[0] != YESCRYPT_ROM_TAG1 || tag[1] != YESCRYPT_ROM_TAG2)
		return NULL;

	le64enc(digest.uc, tag[2]);
	le64enc(digest.uc + 8, tag[3]);
	le64enc(digest.uc + 16, tag[4]);
	le64enc(digest.uc + 24, tag[5]);

	return &digest;
}

int yescrypt_free_shared(yescrypt_shared_t *shared)
{
	return free_region(shared);
}

int yescrypt_init_local(yescrypt_local_t *local)
{
	init_region(local);
	return 0;
}

int yescrypt_free_local(yescrypt_local_t *local)
{
	return free_region(local);
}
