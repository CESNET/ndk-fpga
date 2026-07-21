/*!
 * \file siphash.sv
 * \brief SystemVerilog implementation of SipHash and HalfSipHash cryptographic hash function.
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

`ifndef SIPHASH_SV
`define SIPHASH_SV

`define ROTL64(x, b) (((x) << (b)) | ((x) >> (64 - (b))))
`define ROTL32(x, b) (((x) << (b)) | ((x) >> (32 - (b))))

`define SIPROUND          \
begin                     \
    v0 += v1;             \
    v1 = `ROTL64(v1, 13); \
    v1 ^= v0;             \
    v0 = `ROTL64(v0, 32); \
    v2 += v3;             \
    v3 = `ROTL64(v3, 16); \
    v3 ^= v2;             \
    v0 += v3;             \
    v3 = `ROTL64(v3, 21); \
    v3 ^= v0;             \
    v2 += v1;             \
    v1 = `ROTL64(v1, 17); \
    v1 ^= v2;             \
    v2 = `ROTL64(v2, 32); \
end

`define HALFSIPROUND      \
begin                     \
    v0 += v1;             \
    v1 = `ROTL32(v1, 5);  \
    v1 ^= v0;             \
    v0 = `ROTL32(v0, 16); \
    v2 += v3;             \
    v3 = `ROTL32(v3, 8);  \
    v3 ^= v2;             \
    v0 += v3;             \
    v3 = `ROTL32(v3, 7);  \
    v3 ^= v0;             \
    v2 += v1;             \
    v1 = `ROTL32(v1, 13); \
    v1 ^= v2;             \
    v2 = `ROTL32(v2, 16); \
end

package siphash_pkg;

    class SipHash #(KEY_WIDTH);
    // public interface

        // most used, good balance between security and speed, 64-bit output
        static function logic[64-1 : 0] Hash_2_4(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed // 128-bit seed (secret key in SipHash terminology)
        );
            return SipHash::Hash_c_d(key, seed, 2, 4);
        endfunction

        // better security than the 2-4 variant, 64-bit output
        static function logic[64-1 : 0] Hash_4_8(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed // 128-bit seed (secret key in SipHash terminology)
        );
            return SipHash::Hash_c_d(key, seed, 4, 8);
        endfunction

        // extended version of the regular 2-4 variant, 128-bit output
        static function logic[128-1 : 0] Hash_2_4_128(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed // 128-bit seed (secret key in SipHash terminology)
        );
            return SipHash::Hash_c_d_128(key, seed, 2, 4);
        endfunction

        // extended version of the regular 4-8 variant, 128-bit output
        static function logic[128-1 : 0] Hash_4_8_128(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed // 128-bit seed (secret key in SipHash terminology)
        );
            return SipHash::Hash_c_d_128(key, seed, 4, 8);
        endfunction

        // regular SipHash with configurable compression and finalization rounds, 64-bit output
        static function logic[64-1 : 0] Hash_c_d(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed,     // 128-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds  // number of finalization rounds
        );
            return SipHash::Hash(key, seed, c_rounds, d_rounds, 8)[64-1 : 0];
        endfunction

        // extended SipHash with configurable compression and finalization rounds, 128-bit output
        static function logic[128-1 : 0] Hash_c_d_128(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed,     // 128-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds  // number of finalization rounds
        );
            return SipHash::Hash(key, seed, c_rounds, d_rounds, 16);
        endfunction

    // private
        local static function logic[128-1 : 0] Hash(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[128-1 : 0]       seed,     // 128-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds, // number of finalization rounds
            byte unsigned          outlen    // length of the output in bytes, must be 8 or 16
        );
            const longint unsigned byte_count = KEY_WIDTH / 8;
            const longint unsigned word_count = byte_count / 8;
            const int unsigned left = byte_count & 7;

            logic[64-1 : 0] v0    = 64'h736f6d6570736575;
            logic[64-1 : 0] v1    = 64'h646f72616e646f6d;
            logic[64-1 : 0] v2    = 64'h6c7967656e657261;
            logic[64-1 : 0] v3    = 64'h7465646279746573;
            logic[64-1 : 0] b     = 64'(byte_count) << 56;
            logic[64-1 : 0] hash1 = 64'h00;
            logic[64-1 : 0] hash2 = 64'h00;

            assert(outlen == 8 || outlen == 16)
            else
            begin
                $fatal(1, "SipHash::Hash: outlen must be 8 or 16, got %d.", outlen);
            end

            v3 ^= seed[128-1 : 64];
            v2 ^= seed[ 64-1 :  0];
            v1 ^= seed[128-1 : 64];
            v0 ^= seed[ 64-1 :  0];

            if (outlen == 16)
            begin
                v1 ^= 64'hee;
            end

            for (int i = 0; i < word_count; i++)
            begin
                v3 ^= key[i * 64 +: 64];

                for (int j = 0; j < c_rounds; j++)
                begin
                    `SIPROUND;
                end

                v0 ^= key[i * 64 +: 64];
            end

            if (left == 7)
            begin
                b |= key[(word_count * 64) + 48 +: 8] << 48;
            end
            if (left >= 6)
            begin
                b |= key[(word_count * 64) + 40 +: 8] << 40;
            end
            if (left >= 5)
            begin
                b |= key[(word_count * 64) + 32 +: 8] << 32;
            end
            if (left >= 4)
            begin
                b |= key[(word_count * 64) + 24 +: 8] << 24;
            end
            if (left >= 3)
            begin
                b |= key[(word_count * 64) + 16 +: 8] << 16;
            end
            if (left >= 2)
            begin
                b |= key[(word_count * 64) + 8 +: 8] << 8;
            end
            if (left >= 1)
            begin
                b |= key[(word_count * 64) +: 8];
            end

            v3 ^= b;

            for (int i = 0; i < c_rounds; i++)
            begin
                `SIPROUND;
            end

            v0 ^= b;

            if (outlen == 16)
            begin
                v2 ^= 64'hee;
            end
            else
            begin
                v2 ^= 64'hff;
            end

            for (int i = 0; i < d_rounds; i++)
            begin
                `SIPROUND;
            end

            hash1 = v0 ^ v1 ^ v2 ^ v3;

            if (outlen == 8)
            begin
                return {hash2, hash1};
            end

            v1 ^= 64'hdd;

            for (int i = 0; i < d_rounds; i++)
            begin
                `SIPROUND;
            end

            hash2 = v0 ^ v1 ^ v2 ^ v3;
            return {hash2, hash1};
        endfunction
    endclass

    class HalfSipHash #(KEY_WIDTH);
    // public interface

        // most used, good balance between security and speed, 32-bit output
        static function logic[32-1 : 0] Hash_2_4(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed // 64-bit seed (secret key in SipHash terminology)
        );
            return HalfSipHash::Hash_c_d(key, seed, 2, 4);
        endfunction

        // better security than the 2-4 variant, 32-bit output
        static function logic[32-1 : 0] Hash_4_8(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed // 64-bit seed (secret key in SipHash terminology)
        );
            return HalfSipHash::Hash_c_d(key, seed, 4, 8);
        endfunction

        // extended version of the regular 2-4 variant, 64-bit output
        static function logic[64-1 : 0] Hash_2_4_64(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed // 64-bit seed (secret key in SipHash terminology)
        );
            return HalfSipHash::Hash_c_d_64(key, seed, 2, 4);
        endfunction

        // extended version of the regular 4-8 variant, 64-bit output
        static function logic[64-1 : 0] Hash_4_8_64(
            logic[KEY_WIDTH-1 : 0] key, // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed // 64-bit seed (secret key in SipHash terminology)
        );
            return HalfSipHash::Hash_c_d_64(key, seed, 4, 8);
        endfunction

        // regular siphash with configurable compression and finalization rounds, 32-bit output
        static function logic[32-1 : 0] Hash_c_d(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed,     // 64-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds  // number of finalization rounds
        );
            return HalfSipHash::Hash(key, seed, c_rounds, d_rounds, 4)[32-1 : 0];
        endfunction

        // extended siphash with configurable conpression and finalization rounds, 64-bit output
        static function logic[64-1 : 0] Hash_c_d_64(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed,     // 64-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds  // number of finalization rounds
        );
            return HalfSipHash::Hash(key, seed, c_rounds, d_rounds, 8);
        endfunction

    // private
        local static function logic[64-1 : 0] Hash(
            logic[KEY_WIDTH-1 : 0] key,      // key to be hashed (message in SipHash terminology)
            logic[64-1 : 0]        seed,     // 64-bit seed (secret key in SipHash terminology)
            byte unsigned          c_rounds, // number of compression rounds
            byte unsigned          d_rounds, // number of finalization rounds
            byte unsigned          outlen    // length of the output in bytes, must be 4 or 8
        );
            const int unsigned byte_count = KEY_WIDTH / 8;
            const int unsigned word_count = byte_count / 4;
            const int unsigned left = byte_count & 3;

            logic[32-1 : 0] v0    = 32'h00;
            logic[32-1 : 0] v1    = 32'h00;
            logic[32-1 : 0] v2    = 32'h6c796765;
            logic[32-1 : 0] v3    = 32'h74656462;
            logic[32-1 : 0] b     = 32'(byte_count) << 24;
            logic[32-1 : 0] hash1 = 32'h00;
            logic[32-1 : 0] hash2 = 32'h00;

            assert(outlen == 4 || outlen == 8)
            else
            begin
                $fatal(1, "HalfSipHash::Hash: outlen must be 4 or 8, got %d.", outlen);
            end

            v3 ^= seed[64-1 : 32];
            v2 ^= seed[32-1 :  0];
            v1 ^= seed[64-1 : 32];
            v0 ^= seed[32-1 :  0];

            if (outlen == 8)
            begin
                v1 ^= 32'hee;
            end

            for (int i = 0; i < word_count; i++)
            begin
                v3 ^= key[i * 32 +: 32];

                for (int j = 0; j < c_rounds; j++)
                begin
                    `HALFSIPROUND;
                end

                v0 ^= key[i * 32 +: 32];
            end

            if (left == 3)
            begin
                b |= key[(word_count * 32) + 16 +: 8] << 16;
            end
            if (left >= 2)
            begin
                b |= key[(word_count * 32) + 8 +: 8] << 8;
            end
            if (left >= 1)
            begin
                b |= key[(word_count * 32) +: 8];
            end

            v3 ^= b;

            for (int i = 0; i < c_rounds; i++)
            begin
                `HALFSIPROUND;
            end

            v0 ^= b;

            if (outlen == 8)
            begin
                v2 ^= 32'hee;
            end
            else
            begin
                v2 ^= 32'hff;
            end

            for (int i = 0; i < d_rounds; i++)
            begin
                `HALFSIPROUND;
            end

            hash1 = v1 ^ v3;

            if (outlen == 4)
            begin
                return {hash2, hash1};
            end

            v1 ^= 32'hdd;

            for (int i = 0; i < d_rounds; i++)
            begin
                `HALFSIPROUND;
            end

            hash2 = v1 ^ v3;
            return {hash2, hash1};
        endfunction
    endclass
endpackage
`endif
