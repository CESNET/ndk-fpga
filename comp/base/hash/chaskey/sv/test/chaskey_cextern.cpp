/*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright (C) 2026 CESNET z. s. p. o.
 * Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

 * Interface for reference C++ implementation of Chaskey
 * hash function in chaskey.cpp to be used by DPI-C.
*/

#include <cstdint>
#include <stdio.h>

#include "../../sw/chaskey.h"
#include "chaskey_dpi.h"

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

    uint64_t Chaskey_8_64(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return Chaskey::Hash_8_64((const void*)key_bytes, (size_t)length, seed1, seed2);
    }

    uint64_t Chaskey_12_64(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return Chaskey::Hash_12_64((const void*)key_bytes, (size_t)length, seed1, seed2);
    }

    void Chaskey_8_128(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2, uint64_t* hash1, uint64_t* hash2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        *hash1 = seed1;
        *hash2 = seed2;

        Chaskey::Hash_8_128((const void*)key_bytes, (size_t)length, hash1, hash2);
    }

    void Chaskey_12_128(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2, uint64_t* hash1, uint64_t* hash2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        *hash1 = seed1;
        *hash2 = seed2;

        Chaskey::Hash_12_128((const void*)key_bytes, (size_t)length, hash1, hash2);
    }
}
