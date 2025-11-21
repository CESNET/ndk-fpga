
/*!
 * \file testbench.sv
 * \brief Testbench for the SystemVerilog implementation of SipHash and HalfSipHash cryptographic functions.
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

import siphash_pkg::*;

// define KEY_WIDTH during compilation.
parameter KEY_WIDTH = `KEY_WIDTH;

typedef longint unsigned uint64_t;
typedef int unsigned uint32_t;

import "DPI-C" function uint64_t C_SipHash_2_4(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed1,
    input uint64_t seed2
    );

import "DPI-C" function uint64_t C_SipHash_4_8(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed1,
    input uint64_t seed2
    );

import "DPI-C" function void C_SipHash_2_4_128(
    input  logic[KEY_WIDTH-1 : 0] key,
    input  uint64_t length,
    input  uint64_t seed1,
    input  uint64_t seed2,
    output uint64_t hash1,
    output uint64_t hash2
    );

import "DPI-C" function void C_SipHash_4_8_128(
    input  logic[KEY_WIDTH-1 : 0] key,
    input  uint64_t length,
    input  uint64_t seed1,
    input  uint64_t seed2,
    output uint64_t hash1,
    output uint64_t hash2
    );

import "DPI-C" function uint32_t C_HalfSipHash_2_4(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed
    );

import "DPI-C" function uint32_t C_HalfSipHash_4_8(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed
    );

import "DPI-C" function uint64_t C_HalfSipHash_2_4_64(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed
    );

import "DPI-C" function uint64_t C_HalfSipHash_4_8_64(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed
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
        logic[ 64-1 : 0] seed1;
        logic[ 64-1 : 0] seed2;
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

            $display("generated key=%x, seed1=%x, seed2=%x", key, seed1, seed2);

            // checking SipHash_2_4
            hash[64-1 : 0] = SipHash #(KEY_WIDTH)::Hash_2_4(key, {seed2, seed1});
            c_hash64_1 = C_SipHash_2_4(key, KEY_WIDTH / 8, seed1, seed2);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "SipHash_2_4: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end

            // checking SipHash_4_8
            hash[64-1 : 0] = SipHash #(KEY_WIDTH)::Hash_4_8(key, {seed2, seed1});
            c_hash64_1 = C_SipHash_4_8(key, KEY_WIDTH / 8, seed1, seed2);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "SipHash_4_8: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end

            // checking SipHash_2_4_128
            c_hash64_1 = seed1;
            c_hash64_2 = seed2;

            hash = SipHash #(KEY_WIDTH)::Hash_2_4_128(key, {seed2, seed1});
            C_SipHash_2_4_128(key, KEY_WIDTH / 8, seed1, seed2, c_hash64_1, c_hash64_2);

            assert (hash[64-1 : 0] == c_hash64_1 && hash[128-1 : 64] == c_hash64_2)
            else
            begin
                $fatal(1, "SipHash_2_4_128: Expected %x%x, but got %x", c_hash64_2, c_hash64_1, hash);
            end

            // checking SipHash_4_8_128
            c_hash64_1 = seed1;
            c_hash64_2 = seed2;

            hash = SipHash #(KEY_WIDTH)::Hash_4_8_128(key, {seed2, seed1});
            C_SipHash_4_8_128(key, KEY_WIDTH / 8, seed1, seed2, c_hash64_1, c_hash64_2);

            assert (hash[64-1 : 0] == c_hash64_1 && hash[128-1 : 64] == c_hash64_2)
            else
            begin
                $fatal(1, "SipHash_4_8_128: Expected %x%x, but got %x", c_hash64_2, c_hash64_1, hash);
            end

            // checking HalfSipHash_2_4
            hash[32-1 : 0] = HalfSipHash #(KEY_WIDTH)::Hash_2_4(key, seed1);
            c_hash32 = C_HalfSipHash_2_4(key, KEY_WIDTH / 8, seed1);

            assert (hash[32-1 : 0] == c_hash32)
            else
            begin
                $fatal(1, "HalfSipHash_2_4: Expected %x, but got %x", c_hash32, hash[32-1 : 0]);
            end

            // checking HalfSipHash_4_8
            hash[32-1 : 0] = HalfSipHash #(KEY_WIDTH)::Hash_4_8(key, seed1);
            c_hash32 = C_HalfSipHash_4_8(key, KEY_WIDTH / 8, seed1);

            assert (hash[32-1 : 0] == c_hash32)
            else
            begin
                $fatal(1, "HalfSipHash_4_8: Expected %x, but got %x", c_hash32, hash[32-1 : 0]);
            end

            // checking HalfSipHash_2_4_64
            hash[64-1 : 0] = HalfSipHash #(KEY_WIDTH)::Hash_2_4_64(key, seed1);
            c_hash64_1 = C_HalfSipHash_2_4_64(key, KEY_WIDTH / 8, seed1);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "HalfSipHash_2_4_64: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end

            // checking SipHash_4_8_64
            hash[64-1 : 0] = HalfSipHash #(KEY_WIDTH)::Hash_4_8_64(key, seed1);
            c_hash64_1 = C_HalfSipHash_4_8_64(key, KEY_WIDTH / 8, seed1);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "HalfSipHash_4_8_64: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end
        end
    end
endmodule
