// SPDX-License-Identifier: BSD-3-Clause
// Copyright (C) 2026 CESNET z. s. p. o
// Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

// Majority of the code has been carried over from
// SMHasher3 Chaskey C++ implementation available at
// https://gitlab.com/fwojcik/smhasher3/-/blob/main/hashes/chaskey.cpp

#include "chaskey.h"

#define ROTL32(x, b) (uint32_t)(((x) << (b)) | ((x) >> (32 - (b))))

#define ROUND(v)                                             \
    do {                                                     \
        v[0] += v[1]; v[1] = ROTL32(v[1],  5);               \
        v[1] ^= v[0]; v[0] = ROTL32(v[0], 16);               \
        v[2] += v[3]; v[3] = ROTL32(v[3],  8); v[3] ^= v[2]; \
        v[0] += v[3]; v[3] = ROTL32(v[3], 13); v[3] ^= v[0]; \
        v[2] += v[1]; v[1] = ROTL32(v[1],  7);               \
        v[1] ^= v[2]; v[2] = ROTL32(v[2], 16);               \
    } while (0)

static const volatile uint32_t C[2] = {0x00, 0x87};

#define TIMESTWO(in, out)                       \
    do {                                        \
        out[0] = (in[0] << 1) ^ C[in[3] >> 31]; \
        out[1] = (in[1] << 1) | (in[0] >> 31);  \
        out[2] = (in[2] << 1) | (in[1] >> 31);  \
        out[3] = (in[3] << 1) | (in[2] >> 31);  \
    } while (0)

typedef struct {
    uint32_t  k[4];
    uint32_t  k1[4];
    uint32_t  k2[4];
} keys_t;

void Chaskey::Hash(
    const void *message, // message to be hashed
    size_t length,       // length of the message in bytes
    uint8_t rounds,      // number of permutation rounds
    uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
    uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
)
{
    keys_t key;

    union
    {
        uint8_t *p8;
        uint32_t *p32;
    } m;

    m.p8 = (uint8_t*) message;
    const uint8_t * end = m.p8 + (((length - 1) >> 4) << 4); /* pointer to last message block */

    key.k[0] = (*hash1)       & 0xFFFFFFFF;
    key.k[1] = (*hash1 >> 32) & 0xFFFFFFFF;
    key.k[2] = (*hash2)       & 0xFFFFFFFF;
    key.k[3] = (*hash2 >> 32) & 0xFFFFFFFF;

    // generating subkeys
    TIMESTWO(key.k,  key.k1);
    TIMESTWO(key.k1, key.k2);

    uint32_t v[4] = {key.k[0], key.k[1], key.k[2], key.k[3]};

    if (length != 0)
    {
        for (; m.p8 != end; m.p8 += 16)
        {
            v[0] ^= m.p32[0];
            v[1] ^= m.p32[1];
            v[2] ^= m.p32[2];
            v[3] ^= m.p32[3];

            for (uint32_t i = 0; i < rounds; i++)
            {
                ROUND(v);
            }
        }
    }

    const size_t    remain = length & 0xF;
    const uint32_t* lastblock;
    const uint32_t* lastkey;

    union
    {
        uint8_t  p8[16];
        uint32_t p32[4];
    } lb;

    if (length != 0 && remain == 0)
    {
        lastkey   = key.k1;
        lastblock = m.p32;
    }
    else
    {
        lastkey = key.k2;
        memset(lb.p8, 0, sizeof(lb.p8));
        memcpy(lb.p8, m.p8, remain);
        lb.p8[remain] = 0x01; /* padding bit */
        lastblock = lb.p32;
    }

    v[0] ^= lastblock[0];
    v[1] ^= lastblock[1];
    v[2] ^= lastblock[2];
    v[3] ^= lastblock[3];

    v[0] ^= lastkey[0];
    v[1] ^= lastkey[1];
    v[2] ^= lastkey[2];
    v[3] ^= lastkey[3];

    for (uint32_t i = 0; i < rounds; i++)
    {
        ROUND(v);
    }

    v[0] ^= lastkey[0];
    v[1] ^= lastkey[1];
    v[2] ^= lastkey[2];
    v[3] ^= lastkey[3];

    *hash1 = ((uint64_t)v[1] << 32) | v[0];
    *hash2 = ((uint64_t)v[3] << 32) | v[2];
}
