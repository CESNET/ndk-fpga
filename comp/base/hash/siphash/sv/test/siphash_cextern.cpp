/*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright (C) 2025 CESNET z. s. p. o.
 * Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

 * Interface for reference C++ implementation of SipHash
 * and HalfSipHash in siphash.cpp to be used by DPI-C.
*/

#include <cstdint>
#include <stdio.h>

#include "../../sw/siphash.h"
#include "siphash_dpi.h"

extern "C" {
    void svLogicVecVal_to_bytearray(const svLogicVecVal* vec, uint64_t length, uint8_t* bytearray)
    {
        uint8_t vec_offset = 0;

        for (int i = 0; i < length; i++)
        {
            bytearray[i] = *(((uint8_t*)&(vec + vec_offset)->aval) + (i % 4));
            if (i % 4 == 3) vec_offset++;
        }
    }

    // SipHash
    uint64_t C_SipHash_2_4(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return SipHash::Hash_2_4((const void*)key_bytes, (size_t)length, seed1, seed2);
    }

    uint64_t C_SipHash_4_8(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return SipHash::Hash_4_8((const void*)key_bytes, (size_t)length, seed1, seed2);
    }

    void C_SipHash_2_4_128(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2, uint64_t* hash1, uint64_t* hash2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        *hash1 = seed1;
        *hash2 = seed2;

        SipHash::Hash_2_4_128((const void*)key_bytes, (size_t)length, hash1, hash2);
    }

    void C_SipHash_4_8_128(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2, uint64_t* hash1, uint64_t* hash2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        *hash1 = seed1;
        *hash2 = seed2;

        SipHash::Hash_4_8_128((const void*)key_bytes, (size_t)length, hash1, hash2);
    }

    // HalfSipHash
    uint32_t C_HalfSipHash_2_4(const svLogicVecVal* key, uint64_t length, uint64_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return HalfSipHash::Hash_2_4((const void*)key_bytes, (size_t)length, seed);
    }

    uint32_t C_HalfSipHash_4_8(const svLogicVecVal* key, uint64_t length, uint64_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return HalfSipHash::Hash_4_8((const void*)key_bytes, (size_t)length, seed);
    }

    uint64_t C_HalfSipHash_2_4_64(const svLogicVecVal* key, uint64_t length, uint64_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return HalfSipHash::Hash_2_4_64((const void*)key_bytes, (size_t)length, seed);
    }

    uint64_t C_HalfSipHash_4_8_64(const svLogicVecVal* key, uint64_t length, uint64_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return HalfSipHash::Hash_4_8_64((const void*)key_bytes, (size_t)length, seed);
    }
}
