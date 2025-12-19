// SPDX-License-Identifier: BSD-3-Clause
// Copyright (C) 2025 CESNET z. s. p. o
// Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
//
// Majority of the code has been carried over from
// SipHash reference C implementation available at
// https://github.com/veorq/SipHash

#include <stddef.h>
#include <cstdint>
#include <cassert>

class SipHash
{
    public:
        // most used, good balance between security and speed, 64-bit output
        static uint64_t Hash_2_4(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            return SipHash::Hash_c_d(message, length, 2, 4, key1, key2);
        }

        // better security than the 2-4 variant, 64-bit output
        static uint64_t Hash_4_8(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            return SipHash::Hash_c_d(message, length, 4, 8, key1, key2);
        }

        // extended version of the regular 2-4 variant, 128-bit output
        static void Hash_2_4_128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            SipHash::Hash_c_d_128(message, length, 2, 4, hash1, hash2);
        }

        // extended version of the regular 4-8 variant, 128-bit output
        static void Hash_4_8_128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            SipHash::Hash_c_d_128(message, length, 4, 8, hash1, hash2);
        }

        // regular siphash with configurable compression and finalization rounds, 64-bit output
        static uint64_t Hash_c_d(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t key1,       // lower 64-bits of the key
            uint64_t key2        // higher 64-bits of the key
        )
        {
            uint64_t hash1 = key1;
            uint64_t hash2 = key2;

            SipHash::Hash(message, length, 8, c_rounds, d_rounds, &hash1, &hash2);

            return hash1;
        }

        // extended siphash with configurable conpression and finalization rounds, 128-bit output
        static void Hash_c_d_128(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        )
        {
            SipHash::Hash(message, length, 16, c_rounds, d_rounds, hash1, hash2);
        }

    private:
        static void Hash(
            const void *message, // message to be hashed
            size_t in_length,    // length of the message in bytes
            size_t out_length,   // length of the output in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t *hash1,     // in/out: lower 64-bits of the key, lower 64-bits of the hash
            uint64_t *hash2      // in/out: higher 64-bits of the key, higher 64-bits of the hash
        );
};

class HalfSipHash
{
    public:
        // most used, good balance between security and speed, 32-bit output
        static uint32_t Hash_2_4(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key         // 64-bit key
        )
        {
            return HalfSipHash::Hash_c_d(message, length, 2, 4, key);
        }

        // better security than the 2-4 variant, 32-bit output
        static uint32_t Hash_4_8(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key         // 64-bit key
        )
        {
            return HalfSipHash::Hash_c_d(message, length, 4, 8, key);
        }

        // extended version of the regular 2-4 variant, 64-bit output
        static uint64_t Hash_2_4_64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key         // 64-bit key
        )
        {
            return HalfSipHash::Hash_c_d_64(message, length, 2, 4, key);
        }

        // extended version of the regular 4-8 variant, 64-bit output
        static uint64_t Hash_4_8_64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint64_t key         // 64-bit key
        )
        {
            return HalfSipHash::Hash_c_d_64(message, length, 4, 8, key);
        }

        // regular siphash with configurable compression and finalization rounds, 32-bit output
        static uint32_t Hash_c_d(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t key         // 64-bit key
        )
        {
            return (uint32_t)HalfSipHash::Hash(message, length, 4, c_rounds, d_rounds, key);
        }

        // extended siphash with configurable conpression and finalization rounds, 64-bit output
        static uint64_t Hash_c_d_64(
            const void *message, // message to be hashed
            size_t length,       // length of the message in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t key         // 64-bit key
        )
        {
            return HalfSipHash::Hash(message, length, 8, c_rounds, d_rounds, key);
        }

    private:
        static uint64_t Hash(
            const void *message, // message to be hashed
            size_t in_length,    // length of the message in bytes
            size_t out_length,   // length of the output in bytes
            uint8_t c_rounds,    // number of compression rounds
            uint8_t d_rounds,    // number of finalization rounds
            uint64_t key         // 64-bit key
        );
};
