// SPDX-License-Identifier: BSD-3-Clause
// Copyright (C) 2026 CESNET z. s. p. o
// Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

// Majority of the code has been carried over from
// SMHasher3 Chaskey C++ implementation available at
// https://gitlab.com/fwojcik/smhasher3/-/blob/main/hashes/chaskey.cpp?ref_type=heads

#include <stddef.h>
#include <cstdint>
#include <cassert>
#include <cstring>

class Chaskey
{
    public:
        static uint64_t Hash_8_64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            return Chaskey::Hash64(message, length, 8, key1, key2);
        }

        static uint64_t Hash_12_64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            return Chaskey::Hash64(message, length, 12, key1, key2);
        }

        static uint64_t Hash64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t rounds,      // number of permutation rounds
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            uint64_t hash1 = key1;
            uint64_t hash2 = key2;

            Chaskey::Hash(message, length, rounds, &hash1, &hash2);

            return hash1;
        }

        static void Hash_8_128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            Chaskey::Hash128(message, length, 8, hash1, hash2);
        }

        static void Hash_12_128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            Chaskey::Hash128(message, length, 12, hash1, hash2);
        }

        static void Hash128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t rounds,      // number of permutation rounds
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            Chaskey::Hash(message, length, rounds, hash1, hash2);
        }

    private:
        static void Hash(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t rounds,      // number of permutation rounds
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        );
};
