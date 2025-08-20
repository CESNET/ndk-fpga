/*!
 * \file spookyhash.sv
 * \brief Test for SystemVerilog implementation of short version of SpookyHash non-cryptographic hash function.
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

`ifndef SPOOKYHASH_SV
`define SPOOKYHASH_SV

package spookyhash_pkg;
    typedef int unsigned uint32_t;
    typedef longint unsigned uint64_t;

    class SpookyHash #(KEY_WIDTH);
    // public interface
        static function logic[128-1 : 0] Hash128(logic[KEY_WIDTH : 0] key, uint64_t seed1 = 0, uint64_t seed2 = 0);
            return Short(key, seed1, seed2);
        endfunction

        static function logic[64-1 : 0] Hash64(logic[KEY_WIDTH : 0] key, uint64_t seed = 0);
            logic[128-1 : 0] hash = Short(key, seed, seed);
            return hash[64-1 : 0];
        endfunction

        static function logic[32-1 : 0] Hash32(logic[KEY_WIDTH : 0] key, uint32_t seed = 0);
            logic[128-1 : 0] hash = Short(key, seed, seed);
            return hash[32-1 : 0];
        endfunction

    // private
        local typedef struct {
            logic[64-1 : 0] a;
            logic[64-1 : 0] b;
            logic[64-1 : 0] c;
            logic[64-1 : 0] d;
        } hash_vars_t;

        local static const uint64_t sc_const = 64'hdeadbeefdeadbeef;

        local static function logic[64-1 : 0] Rot64(logic[64-1 : 0] x, int k);
            return (x << k) | (x >> (64 - k));
        endfunction

        local static function hash_vars_t ShortMix(hash_vars_t hvars);
            hvars.c = Rot64(hvars.c,50);  hvars.c += hvars.d;  hvars.a ^= hvars.c;
            hvars.d = Rot64(hvars.d,52);  hvars.d += hvars.a;  hvars.b ^= hvars.d;
            hvars.a = Rot64(hvars.a,30);  hvars.a += hvars.b;  hvars.c ^= hvars.a;
            hvars.b = Rot64(hvars.b,41);  hvars.b += hvars.c;  hvars.d ^= hvars.b;
            hvars.c = Rot64(hvars.c,54);  hvars.c += hvars.d;  hvars.a ^= hvars.c;
            hvars.d = Rot64(hvars.d,48);  hvars.d += hvars.a;  hvars.b ^= hvars.d;
            hvars.a = Rot64(hvars.a,38);  hvars.a += hvars.b;  hvars.c ^= hvars.a;
            hvars.b = Rot64(hvars.b,37);  hvars.b += hvars.c;  hvars.d ^= hvars.b;
            hvars.c = Rot64(hvars.c,62);  hvars.c += hvars.d;  hvars.a ^= hvars.c;
            hvars.d = Rot64(hvars.d,34);  hvars.d += hvars.a;  hvars.b ^= hvars.d;
            hvars.a = Rot64(hvars.a,5);   hvars.a += hvars.b;  hvars.c ^= hvars.a;
            hvars.b = Rot64(hvars.b,36);  hvars.b += hvars.c;  hvars.d ^= hvars.b;

            return hvars;
        endfunction

        local static function hash_vars_t ShortEnd(hash_vars_t hvars);
            hvars.d ^= hvars.c;  hvars.c = Rot64(hvars.c,15);  hvars.d += hvars.c;
            hvars.a ^= hvars.d;  hvars.d = Rot64(hvars.d,52);  hvars.a += hvars.d;
            hvars.b ^= hvars.a;  hvars.a = Rot64(hvars.a,26);  hvars.b += hvars.a;
            hvars.c ^= hvars.b;  hvars.b = Rot64(hvars.b,51);  hvars.c += hvars.b;
            hvars.d ^= hvars.c;  hvars.c = Rot64(hvars.c,28);  hvars.d += hvars.c;
            hvars.a ^= hvars.d;  hvars.d = Rot64(hvars.d,9);   hvars.a += hvars.d;
            hvars.b ^= hvars.a;  hvars.a = Rot64(hvars.a,47);  hvars.b += hvars.a;
            hvars.c ^= hvars.b;  hvars.b = Rot64(hvars.b,54);  hvars.c += hvars.b;
            hvars.d ^= hvars.c;  hvars.c = Rot64(hvars.c,32);  hvars.d += hvars.c;
            hvars.a ^= hvars.d;  hvars.d = Rot64(hvars.d,25);  hvars.a += hvars.d;
            hvars.b ^= hvars.a;  hvars.a = Rot64(hvars.a,63);  hvars.b += hvars.a;

            return hvars;
        endfunction

        local static function logic[128-1 : 0] Short(logic[KEY_WIDTH : 0] key, uint64_t seed1 = 0, uint64_t seed2 = 0);
            uint64_t length = KEY_WIDTH / 8;
            int unsigned remainder = length % 32;
            hash_vars_t hvars = '{seed1, seed2, sc_const, sc_const};
            logic[128-1 : 0] hash;

            if (length > 15)
            begin
                for (uint64_t i = 0; i < length / 32; i++)
                begin
                    hvars.c += key[64-1 : 0];
                    hvars.d += key[128-1 : 64];
                    hvars    = ShortMix(hvars);
                    hvars.a += key[192-1 : 128];
                    hvars.b += key[256-1 : 192];
                    key      = key >> 256;
                end

                if (remainder >= 16)
                begin
                    hvars.c   += key[64-1 : 0];
                    hvars.d   += key[128-1 : 64];
                    hvars      = ShortMix(hvars);
                    key        = key >> 128;
                    remainder -= 16;
                end
            end

            hvars.d += length << 56;

            if (remainder >= 12)
            begin
                hvars.d = remainder == 15 ? hvars.d + (key[120-1 : 112] << 48) : hvars.d;
                hvars.d = remainder >= 14 ? hvars.d + (key[112-1 : 104] << 40) : hvars.d;
                hvars.d = remainder >= 13 ? hvars.d + (key[104-1 : 96]  << 32) : hvars.d;

                hvars.c += key[64-1 : 0];
                hvars.d += key[95 : 64];
            end
            else if (remainder >= 8 && remainder < 12)
            begin
                hvars.d = remainder == 11 ? hvars.d + (key[88-1 : 80] << 16) : hvars.d;
                hvars.d = remainder >= 10 ? hvars.d + (key[80-1 : 72] <<  8) : hvars.d;
                hvars.d = remainder >= 9  ? hvars.d + key[72-1 : 64]         : hvars.d;

                hvars.c += key[64-1 : 0];
            end
            else if (remainder >= 4 && remainder < 8)
            begin
                hvars.c = remainder == 7 ? hvars.c + (key[56-1 : 48] << 48) : hvars.c;
                hvars.c = remainder >= 6 ? hvars.c + (key[48-1 : 40] << 40) : hvars.c;
                hvars.c = remainder >= 5 ? hvars.c + (key[40-1 : 32] << 32) : hvars.c;

                hvars.c += key[32-1 : 0];
            end
            else if (remainder >= 1 && remainder < 4)
            begin
                hvars.c = remainder == 3 ? hvars.c + (key[24-1 : 16] << 16) : hvars.c;
                hvars.c = remainder >= 2 ? hvars.c + (key[16-1 : 8]  <<  8) : hvars.c;

                hvars.c += key[7 : 0];
            end
            else
            begin
                hvars.c += sc_const;
                hvars.d += sc_const;
            end

            hvars = ShortEnd(hvars);

            hash[64-1  :  0] = hvars.a;
            hash[128-1 : 64] = hvars.b;

            return hash;
        endfunction
    endclass

endpackage
`endif
