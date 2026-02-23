/*!
 * \file siphash.sv
 * \brief SystemVerilog implementation of Chaskey cryptographic hash function.
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

`ifndef CHASKEY_SV
`define CHASKEY_SV

`define ROTL32(x, b) (((x) << (b)) | ((x) >> (32 - (b))))
`define CEILDIV(n, d) ((n + d - 1) / d)

`define ROUND(v)                                          \
begin                                                     \
    v[0] += v[1]; v[1] = `ROTL32(v[1],  5);               \
    v[1] ^= v[0]; v[0] = `ROTL32(v[0], 16);               \
    v[2] += v[3]; v[3] = `ROTL32(v[3],  8); v[3] ^= v[2]; \
    v[0] += v[3]; v[3] = `ROTL32(v[3], 13); v[3] ^= v[0]; \
    v[2] += v[1]; v[1] = `ROTL32(v[1],  7);               \
    v[1] ^= v[2]; v[2] = `ROTL32(v[2], 16);               \
end

`define TIMESTWO(x) ((x << 1) ^ ((x[127])? 128'h87 : 128'h00))

package chaskey_pkg;

    class Chaskey #(KEY_WIDTH);
    // public interface
        static function logic[128-1 : 0] Hash_8_128(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed
        );
            return Chaskey::Hash128(key, seed, 8);
        endfunction;

        static function logic[128-1 : 0] Hash_12_128(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed
        );
            return Chaskey::Hash128(key, seed, 12);
        endfunction;

        static function logic[128-1 : 0] Hash128(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed,
            byte unsigned          rounds
        );
            return Chaskey::Hash(key, seed, rounds);
        endfunction;

        static function logic[64-1 : 0] Hash_8_64(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed
        );
            return Chaskey::Hash64(key, seed, 8);
        endfunction;

        static function logic[64-1 : 0] Hash_12_64(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed
        );
            return Chaskey::Hash64(key, seed, 12);
        endfunction;

        static function logic[64-1 : 0] Hash64(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed,
            byte unsigned          rounds
        );
            return Chaskey::Hash(key, seed, rounds)[64-1 : 0];
        endfunction;

    // private
        localparam int REMAIN     = KEY_WIDTH % 128;
        localparam int MAX_OFFSET = (`CEILDIV(KEY_WIDTH, 128) - 1) * 128;

        local static function logic[128-1 : 0] Hash(
            logic[KEY_WIDTH-1 : 0] key,
            logic[128-1 : 0]       seed,
            byte unsigned          rounds
        );
            logic[4-1 : 0][32-1 : 0] v = {
                seed[128-1 : 96],
                seed[ 96-1 : 64],
                seed[ 64-1 : 32],
                seed[ 32-1 :  0]
            };

            logic[128-1 : 0] lastkey   = 128'h00;
            logic[128-1 : 0] lastblock = 128'h00;

            for (int offset = 0; offset < MAX_OFFSET; offset += 128)
            begin

                v[0] ^= key[offset +  0 +: 32];
                v[1] ^= key[offset + 32 +: 32];
                v[2] ^= key[offset + 64 +: 32];
                v[3] ^= key[offset + 96 +: 32];

                for (int i = 0; i < rounds; i++)
                begin
                    `ROUND(v);
                end
            end

            if (REMAIN == 0)
            begin
                lastblock = key[MAX_OFFSET +: 128];
                lastkey   = `TIMESTWO(seed);
            end
            else
            begin
                lastblock[REMAIN-1 : 0] = key[MAX_OFFSET +: REMAIN];
                // set last bit as padding
                lastblock[REMAIN] = 1;
                lastkey   = `TIMESTWO(seed);
                lastkey   = `TIMESTWO(lastkey);
            end

            v[0] ^= lastblock[ 32-1 :  0];
            v[1] ^= lastblock[ 64-1 : 32];
            v[2] ^= lastblock[ 96-1 : 64];
            v[3] ^= lastblock[128-1 : 96];

            v[0] ^= lastkey[ 32-1 :  0];
            v[1] ^= lastkey[ 64-1 : 32];
            v[2] ^= lastkey[ 96-1 : 64];
            v[3] ^= lastkey[128-1 : 96];

            for (int i = 0; i < rounds; i++)
            begin
                `ROUND(v);
            end

            v[0] ^= lastkey[ 32-1 :  0];
            v[1] ^= lastkey[ 64-1 : 32];
            v[2] ^= lastkey[ 96-1 : 64];
            v[3] ^= lastkey[128-1 : 96];

            return {v[3], v[2], v[1], v[0]};
        endfunction
    endclass
endpackage;

`endif
