// SPDX-License-Identifier: BSD-3-Clause
// Copyright (C) 2025 CESNET z. s. p. o
// Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
//
// Majority of the code has been carried over from
// SipHash reference C implementation available at
// https://github.com/veorq/SipHash

#include "siphash.h"

#define ROTL64(x, b) (uint64_t)(((x) << (b)) | ((x) >> (64 - (b))))
#define ROTL32(x, b) (uint32_t)(((x) << (b)) | ((x) >> (32 - (b))))

#define U32TO8_LE(p, v)                                                        \
    (p)[0] = (uint8_t)((v));                                                   \
    (p)[1] = (uint8_t)((v) >> 8);                                              \
    (p)[2] = (uint8_t)((v) >> 16);                                             \
    (p)[3] = (uint8_t)((v) >> 24);

#define U64TO8_LE(p, v)                                                        \
    U32TO8_LE((p), (uint32_t)((v)));                                           \
    U32TO8_LE((p) + 4, (uint32_t)((v) >> 32));

#define U8TO64_LE(p)                                                           \
    (((uint64_t)((p)[0])) | ((uint64_t)((p)[1]) << 8) |                        \
     ((uint64_t)((p)[2]) << 16) | ((uint64_t)((p)[3]) << 24) |                 \
     ((uint64_t)((p)[4]) << 32) | ((uint64_t)((p)[5]) << 40) |                 \
     ((uint64_t)((p)[6]) << 48) | ((uint64_t)((p)[7]) << 56))

#define U8TO32_LE(p)                                                           \
    (((uint32_t)((p)[0])) | ((uint32_t)((p)[1]) << 8) |                        \
     ((uint32_t)((p)[2]) << 16) | ((uint32_t)((p)[3]) << 24))

#define SIPROUND                                                               \
    do {                                                                       \
        v0 += v1;                                                              \
        v1 = ROTL64(v1, 13);                                                   \
        v1 ^= v0;                                                              \
        v0 = ROTL64(v0, 32);                                                   \
        v2 += v3;                                                              \
        v3 = ROTL64(v3, 16);                                                   \
        v3 ^= v2;                                                              \
        v0 += v3;                                                              \
        v3 = ROTL64(v3, 21);                                                   \
        v3 ^= v0;                                                              \
        v2 += v1;                                                              \
        v1 = ROTL64(v1, 17);                                                   \
        v1 ^= v2;                                                              \
        v2 = ROTL64(v2, 32);                                                   \
    } while (0)

#define HALFSIPROUND                                                           \
    do {                                                                       \
        v0 += v1;                                                              \
        v1 = ROTL32(v1, 5);                                                    \
        v1 ^= v0;                                                              \
        v0 = ROTL32(v0, 16);                                                   \
        v2 += v3;                                                              \
        v3 = ROTL32(v3, 8);                                                    \
        v3 ^= v2;                                                              \
        v0 += v3;                                                              \
        v3 = ROTL32(v3, 7);                                                    \
        v3 ^= v0;                                                              \
        v2 += v1;                                                              \
        v1 = ROTL32(v1, 13);                                                   \
        v1 ^= v2;                                                              \
        v2 = ROTL32(v2, 16);                                                   \
    } while (0)


#ifdef DEBUG_SIPHASH
#include <stdio.h>

#define TRACE64                                                                \
    do {                                                                       \
        printf("(%3zu) v0 %016" PRIx64 "\n", inlen, v0);                       \
        printf("(%3zu) v1 %016" PRIx64 "\n", inlen, v1);                       \
        printf("(%3zu) v2 %016" PRIx64 "\n", inlen, v2);                       \
        printf("(%3zu) v3 %016" PRIx64 "\n", inlen, v3);                       \
    } while (0)

#define TRACE32                                                                \
    do {                                                                       \
        printf("(%3zu) v0 %08" PRIx32 "\n", inlen, v0);                        \
        printf("(%3zu) v1 %08" PRIx32 "\n", inlen, v1);                        \
        printf("(%3zu) v2 %08" PRIx32 "\n", inlen, v2);                        \
        printf("(%3zu) v3 %08" PRIx32 "\n", inlen, v3);                        \
    } while (0)
#else
#define TRACE64
#define TRACE32
#endif


void SipHash::Hash(
    const void *message, // message to be hashed
    size_t in_length,    // length of the message in bytes
    size_t out_length,   // length of the output in bytes
    uint8_t c_rounds,    // number of compression rounds
    uint8_t d_rounds,    // number of finalization rounds
    uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
    uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
)
{
    assert((out_length == 8) || (out_length == 16));

    const unsigned char *ni = (const unsigned char *)message;

    uint64_t v0 = UINT64_C(0x736f6d6570736575);
    uint64_t v1 = UINT64_C(0x646f72616e646f6d);
    uint64_t v2 = UINT64_C(0x6c7967656e657261);
    uint64_t v3 = UINT64_C(0x7465646279746573);
    uint64_t m;
    uint64_t b = ((uint64_t)in_length) << 56;
    int i;
    const unsigned char *end = ni + in_length - (in_length % sizeof(uint64_t));
    const int left = in_length & 7;

    v3 ^= *hash2;
    v2 ^= *hash1;
    v1 ^= *hash2;
    v0 ^= *hash1;

    if (out_length == 16)
        v1 ^= 0xee;

    for (; ni != end; ni += 8) {
        m = U8TO64_LE(ni);
        v3 ^= m;

        TRACE64;
        for (i = 0; i < c_rounds; ++i)
            SIPROUND;

        v0 ^= m;
    }

    switch (left) {
    case 7:
        b |= ((uint64_t)ni[6]) << 48;
        /* FALLTHRU */
    case 6:
        b |= ((uint64_t)ni[5]) << 40;
        /* FALLTHRU */
    case 5:
        b |= ((uint64_t)ni[4]) << 32;
        /* FALLTHRU */
    case 4:
        b |= ((uint64_t)ni[3]) << 24;
        /* FALLTHRU */
    case 3:
        b |= ((uint64_t)ni[2]) << 16;
        /* FALLTHRU */
    case 2:
        b |= ((uint64_t)ni[1]) << 8;
        /* FALLTHRU */
    case 1:
        b |= ((uint64_t)ni[0]);
        break;
    case 0:
        break;
    }

    v3 ^= b;

    TRACE64;
    for (i = 0; i < c_rounds; ++i)
        SIPROUND;

    v0 ^= b;

    if (out_length == 16)
        v2 ^= 0xee;
    else
        v2 ^= 0xff;

    TRACE64;
    for (i = 0; i < d_rounds; ++i)
        SIPROUND;

    *hash1 = v0 ^ v1 ^ v2 ^ v3;

    if (out_length == 8)
    {
        *hash2 = 0ul;
        return;
    }

    v1 ^= 0xdd;

    TRACE64;
    for (i = 0; i < d_rounds; ++i)
        SIPROUND;

    *hash2 = v0 ^ v1 ^ v2 ^ v3;
    return;
}


uint64_t HalfSipHash::Hash(
    const void *message, // message to be hashed
    size_t in_length,    // length of the message in bytes
    size_t out_length,   // length of the output in bytes
    uint8_t c_rounds,    // number of compression rounds
    uint8_t d_rounds,    // number of finalization rounds
    uint64_t key         // 64-bit key
)
{
    assert((out_length == 4) || (out_length == 8));

    const unsigned char *ni = (const unsigned char *)message;

    uint32_t v0 = 0;
    uint32_t v1 = 0;
    uint32_t v2 = UINT32_C(0x6c796765);
    uint32_t v3 = UINT32_C(0x74656462);
    uint32_t m;
    uint32_t b = ((uint32_t)in_length) << 24;
    uint64_t hash = 0ul;
    int i;
    const unsigned char *end = ni + in_length - (in_length % sizeof(uint32_t));
    const int left = in_length & 3;

    v3 ^= (uint32_t)((key >> 32) & (~(uint32_t)0));
    v2 ^= (uint32_t)(key & (~(uint32_t)0));
    v1 ^= (uint32_t)((key >> 32) & (~(uint32_t)0));
    v0 ^= (uint32_t)(key & (~(uint32_t)0));

    if (out_length == 8)
        v1 ^= 0xee;

    for (; ni != end; ni += 4) {
        m = U8TO32_LE(ni);
        v3 ^= m;

        TRACE32;
        for (i = 0; i < c_rounds; ++i)
            HALFSIPROUND;

        v0 ^= m;
    }

    switch (left) {
    case 3:
        b |= ((uint32_t)ni[2]) << 16;
        /* FALLTHRU */
    case 2:
        b |= ((uint32_t)ni[1]) << 8;
        /* FALLTHRU */
    case 1:
        b |= ((uint32_t)ni[0]);
        break;
    case 0:
        break;
    }

    v3 ^= b;

    TRACE32;
    for (i = 0; i < c_rounds; ++i)
        HALFSIPROUND;

    v0 ^= b;

    if (out_length == 8)
        v2 ^= 0xee;
    else
        v2 ^= 0xff;

    TRACE32;
    for (i = 0; i < d_rounds; ++i)
        HALFSIPROUND;

    hash = (uint64_t)(v1 ^ v3);

    if (out_length == 4)
        return hash;

    v1 ^= 0xdd;

    TRACE32;
    for (i = 0; i < d_rounds; ++i)
        HALFSIPROUND;

    hash += (uint64_t)(v1 ^ v3) << 32;

    return hash;
}
