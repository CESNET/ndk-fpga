
/*!
 * \file testbench.sv
 * \brief Testbench for the SystemVerilog implementation of Chaskey cryptographic hash function.
 * \author Ondrej Schwarz <ondrejschwarz@cesnet.cz>
 * \date 2026
 */
 /*
 * Copyright (C) 2026 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 * SPDX-License-Identifier: BSD-3-Clause
 *
 *
 */

import chaskey_pkg::*;

// define KEY_WIDTH during compilation.
parameter KEY_WIDTH = `KEY_WIDTH;

typedef longint unsigned uint64_t;
typedef int unsigned uint32_t;

import "DPI-C" function uint64_t Chaskey_8_64(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed1,
    input uint64_t seed2
    );

import "DPI-C" function uint64_t Chaskey_12_64(
    input logic[KEY_WIDTH-1 : 0] key,
    input uint64_t length,
    input uint64_t seed1,
    input uint64_t seed2
    );

import "DPI-C" function void Chaskey_8_128(
    input  logic[KEY_WIDTH-1 : 0] key,
    input  uint64_t length,
    input  uint64_t seed1,
    input  uint64_t seed2,
    output uint64_t hash1,
    output uint64_t hash2
    );

import "DPI-C" function void Chaskey_12_128(
    input  logic[KEY_WIDTH-1 : 0] key,
    input  uint64_t length,
    input  uint64_t seed1,
    input  uint64_t seed2,
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
        logic[       64-1 : 0] seed1;
        logic[       64-1 : 0] seed2;
        logic[      128-1 : 0] hash;

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

            // testing Chaskey_8_64
            hash[64-1 : 0] = Chaskey #(KEY_WIDTH)::Hash_8_64(key, {seed2, seed1});
            c_hash64_1 = Chaskey_8_64(key, KEY_WIDTH / 8, seed1, seed2);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "Chaskey_8_64: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end

            // testing Chaskey_12_64
            hash[64-1 : 0] = Chaskey #(KEY_WIDTH)::Hash_12_64(key, {seed2, seed1});
            c_hash64_1 = Chaskey_12_64(key, KEY_WIDTH / 8, seed1, seed2);

            assert (hash[64-1 : 0] == c_hash64_1)
            else
            begin
                $fatal(1, "Chaskey_12_64: Expected %x, but got %x", c_hash64_1, hash[64-1 : 0]);
            end

            // testing Chaskey_8_128
            c_hash64_1 = seed1;
            c_hash64_2 = seed2;

            hash = Chaskey #(KEY_WIDTH)::Hash_8_128(key, {seed2, seed1});
            Chaskey_8_128(key, KEY_WIDTH / 8, seed1, seed2, c_hash64_1, c_hash64_2);

            assert (hash[64-1 : 0] == c_hash64_1 && hash[128-1 : 64] == c_hash64_2)
            else
            begin
                $fatal(1, "Chaskey_8_128: Expected %x%x, but got %x", c_hash64_2, c_hash64_1, hash);
            end

            // testing Chaskey_12_128
            c_hash64_1 = seed1;
            c_hash64_2 = seed2;

            hash = Chaskey #(KEY_WIDTH)::Hash_12_128(key, {seed2, seed1});
            Chaskey_12_128(key, KEY_WIDTH / 8, seed1, seed2, c_hash64_1, c_hash64_2);

            assert (hash[64-1 : 0] == c_hash64_1 && hash[128-1 : 64] == c_hash64_2)
            else
            begin
                $fatal(1, "Chaskey_12_128: Expected %x%x, but got %x", c_hash64_2, c_hash64_1, hash);
            end
        end
    end
endmodule
