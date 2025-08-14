
/*!
 * \file testbench.sv
 * \brief SystemVerilog implementation of short version of SpookyHash non-cryptographic hash function.
 * \author Ondrej Schwarz <ondrejschwarz@cesnet.cz>
 * \date 2025
 */
 /*
 * Copyright (C) 2025 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 */

import spookyhash_pkg::*;

// define KEY_WIDTH during compilation.
parameter KEY_WIDTH = `KEY_WIDTH;

import "DPI-C" function uint32_t C_SpookyHash32(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint32_t seed
    );

import "DPI-C" function uint64_t C_SpookyHash64(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed
    );

import "DPI-C" function void C_SpookyHash128(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed1,
    input uint64_t seed2,
    output uint64_t hash1,
    output uint64_t hash2
    );


module testbench #(KEY_WIDTH = KEY_WIDTH, KEY_CNT=10000);
    static function logic[KEY_WIDTH-1 : 0] random_key();
        static logic[KEY_WIDTH-1 : 0] key = 0;

        for (int i = 0; i < (KEY_WIDTH + 31) / 32; i++)
        begin
            key[(i*32) +: 32] = $urandom();
        end

        return key;
    endfunction

    initial begin
        logic[KEY_WIDTH-1 : 0] key;
        uint64_t seed1;
        uint64_t seed2;
        logic[128-1 : 0] hash;

        uint32_t c_hash32;
        uint64_t c_hash64_1;
        uint64_t c_hash64_2;

        for (int i = 0; i < KEY_CNT; i++)
        begin
            key = random_key();
            seed1[32-1 :  0] = $urandom();
            seed1[64-1 : 32] = $urandom();
            seed2[32-1 :  0] = $urandom();
            seed2[64-1 : 32] = $urandom();

            $display("generated key=%h, seed1=%d, seed2=%d", key, seed1, seed2);

            // comparing 32-bit hashes
            hash[32-1 : 0] = SpookyHash #(KEY_WIDTH)::Hash32(key, seed1);
            c_hash32 = C_SpookyHash32(key, KEY_WIDTH / 8, seed1);

            assert (hash[32-1 : 0] == c_hash32)
            else
            begin
                $fatal(1, "Hash32: Expected: %h, but got %h", c_hash32, hash[32-1 : 0]);
            end

            // comparing 64-bit hashes
            hash[64-1 : 0] = SpookyHash #(KEY_WIDTH)::Hash64(key, seed1);
            c_hash64_1 = C_SpookyHash64(key, KEY_WIDTH / 8, seed1);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "Hash64: Expected %h, but got %h", c_hash64_1, hash[64-1 : 0]);
            end

            // comparing 128-bit hashes
            c_hash64_1 = seed1;
            c_hash64_2 = seed2;

            hash = SpookyHash #(KEY_WIDTH)::Hash128(key, seed1, seed2);
            C_SpookyHash128(key, KEY_WIDTH / 8, seed1, seed2, c_hash64_1, c_hash64_2);

            assert (hash[64-1 : 0] == c_hash64_1 && hash[128-1 : 64] == c_hash64_2)
            else
            begin
                $fatal(1, "Hash128: Expected %h%h, but got %h", c_hash64_2, c_hash64_1, hash);
            end
        end
    end
endmodule
