/*
 * SPDX-License-Identifier: BSD-3-Clause
 * Copyright (C) 2025 CESNET z. s. p. o.
 * Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

 * Interface for reference C++ implementation of spookyhash
 * in SpookyV2.cpp to be used by DPI-C.
*/

#include <cstdint>
#include <stdio.h>

#include "../../sw/SpookyV2.h"
#include "spooky_dpi.h"

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

    uint32_t C_SpookyHash32(const svLogicVecVal* key, uint64_t length, uint32_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return SpookyHash::Hash32((const void*)key_bytes, (size_t)length, seed);
    }

    uint64_t C_SpookyHash64(const svLogicVecVal* key, uint64_t length, uint64_t seed)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        return SpookyHash::Hash64((const void*)key_bytes, (size_t)length, seed);
    }

    void C_SpookyHash128(const svLogicVecVal* key, uint64_t length, uint64_t seed1, uint64_t seed2, uint64_t* hash1, uint64_t* hash2)
    {
        uint8_t key_bytes[length];
        svLogicVecVal_to_bytearray(key, length, key_bytes);

        *hash1 = seed1;
        *hash2 = seed2;

        SpookyHash::Hash128((const void*)key_bytes, (size_t)length, hash1, hash2);
    }
}
