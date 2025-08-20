-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- FW implementation of void ShortMix(uint64 &h0, uint64 &h1, uint64 &h2, uint64 &h3).
entity SPOOKY_SHORTMIX is
    generic (
        -- width of the whole key
        KEY_WIDTH  : natural := 256;
        -- width of the passthrough metadata
        META_WIDTH : natural := 32;
        -- setup of the registers of this component
        REG_SETUP  : std_logic_vector(25-1 downto 0) := "1111111111111111111111111"
    );
    port (
        -- main clock
        CLK        : in std_logic;
        -- synchronious reset
        RESET      : in std_logic;

        -- key remainder
        IN_KEY     : in  unsigned(KEY_WIDTH-1 downto 0);
        -- variables used in hash calculation
        IN_H0      : in  unsigned(64-1 downto 0);
        IN_H1      : in  unsigned(64-1 downto 0);
        IN_H2      : in  unsigned(64-1 downto 0);
        IN_H3      : in  unsigned(64-1 downto 0);
        -- metadata input
        IN_META    : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID   : in  std_logic;

        -- key passthrough
        OUT_KEY    : out unsigned(KEY_WIDTH-1 downto 0);
        -- updated variables
        OUT_H0     : out unsigned(64-1 downto 0);
        OUT_H1     : out unsigned(64-1 downto 0);
        OUT_H2     : out unsigned(64-1 downto 0);
        OUT_H3     : out unsigned(64-1 downto 0);
        -- metadata output
        OUT_META   : out std_logic_vector(META_WIDTH-1 downto 0);
        -- valid passthrough
        OUT_VALID  : out std_logic
    );
end entity;

architecture FULL of SPOOKY_SHORTMIX is
    -- length of the pipeline of this component
    constant PIPE_LENGTH : integer := 25;

    signal h0      : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1      : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2      : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3      : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);

    signal key_reg : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal h0_reg  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1_reg  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2_reg  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3_reg  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);

    signal vld     : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta    : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key_reg(24) <= IN_KEY;
    h0_reg(24)  <= IN_H0;
    h1_reg(24)  <= IN_H1;
    h2_reg(24)  <= IN_H2;
    h3_reg(24)  <= IN_H3;
    vld(24)     <= IN_VALID;
    meta(24)    <= IN_META;

    -- ================================================
    --                     LOGIC
    -- ================================================

    -- h2 = Rot64(h2,50);  h2 += h3;  h0 ^= h2; h3 = Rot64(h3,52);
    h0(24) <= h0_reg(24);
    h1(24) <= h1_reg(24);
    h2(24) <= rotate_left(h2_reg(24), 50);
    h3(24) <= h3_reg(24);

    h0(23) <= h0_reg(23);
    h1(23) <= h1_reg(23);
    h2(23) <= h2_reg(23) + h3_reg(23);
    h3(23) <= h3_reg(23);

    h0(22) <= h0_reg(22) xor h2_reg(22);
    h1(22) <= h1_reg(22);
    h2(22) <= h2_reg(22);
    h3(22) <= rotate_left(h3_reg(22), 52);

    --  h3 += h0;  h1 ^= h3; h0 = Rot64(h0,30);
    h0(21) <= h0_reg(21);
    h1(21) <= h1_reg(21);
    h2(21) <= h2_reg(21);
    h3(21) <= h3_reg(21) + h0_reg(21);

    h0(20) <= rotate_left(h0_reg(20), 30);
    h1(20) <= h1_reg(20) xor h3_reg(20);
    h2(20) <= h2_reg(20);
    h3(20) <= h3_reg(20);

    -- h0 += h1;  h2 ^= h0; h1 = Rot64(h1,41);
    h0(19) <= h0_reg(19) + h1_reg(19);
    h1(19) <= h1_reg(19);
    h2(19) <= h2_reg(19);
    h3(19) <= h3_reg(19);

    h0(18) <= h0_reg(18);
    h1(18) <= rotate_left(h1_reg(18), 41);
    h2(18) <= h2_reg(18) xor h0_reg(18);
    h3(18) <= h3_reg(18);

    -- h1 += h2; h3 ^= h1; h2 = Rot64(h2,54);
    h0(17) <= h0_reg(17);
    h1(17) <= h1_reg(17) + h2_reg(17);
    h2(17) <= h2_reg(17);
    h3(17) <= h3_reg(17);

    h0(16) <= h0_reg(16);
    h1(16) <= h1_reg(16);
    h2(16) <= rotate_left(h2_reg(16), 54);
    h3(16) <= h3_reg(16) xor h1_reg(16);

    -- h2 += h3;  h0 ^= h2; h3 = Rot64(h3,48);
    h0(15) <= h0_reg(15);
    h1(15) <= h1_reg(15);
    h2(15) <= h2_reg(15) + h3_reg(15);
    h3(15) <= h3_reg(15);

    h0(14) <= h0_reg(14) xor h2_reg(14);
    h1(14) <= h1_reg(14);
    h2(14) <= h2_reg(14);
    h3(14) <= rotate_left(h3_reg(14), 48);

    -- h3 += h0;  h1 ^= h3; h0 = Rot64(h0,38);
    h0(13) <= h0_reg(13);
    h1(13) <= h1_reg(13);
    h2(13) <= h2_reg(13);
    h3(13) <= h3_reg(13) + h0_reg(13);

    h0(12) <= rotate_left(h0_reg(12), 38);
    h1(12) <= h1_reg(12) xor h3_reg(12);
    h2(12) <= h2_reg(12);
    h3(12) <= h3_reg(12);

    -- h0 += h1;  h2 ^= h0; h1 = Rot64(h1,37);
    h0(11) <= h0_reg(11) + h1_reg(11);
    h1(11) <= h1_reg(11);
    h2(11) <= h2_reg(11);
    h3(11) <= h3_reg(11);

    h0(10) <= h0_reg(10);
    h1(10) <= rotate_left(h1_reg(10), 37);
    h2(10) <= h2_reg(10) xor h0_reg(10);
    h3(10) <= h3_reg(10);

    -- h1 += h2;  h3 ^= h1;  h2 = Rot64(h2,62);
    h0(9) <= h0_reg(9);
    h1(9) <= h1_reg(9) + h2_reg(9);
    h2(9) <= h2_reg(9);
    h3(9) <= h3_reg(9);

    h0(8) <= h0_reg(8);
    h1(8) <= h1_reg(8);
    h2(8) <= rotate_left(h2_reg(8), 62);
    h3(8) <= h3_reg(8) xor h1_reg(8);

    -- h2 += h3;  h0 ^= h2;  h3 = Rot64(h3,34);
    h0(7) <= h0_reg(7);
    h1(7) <= h1_reg(7);
    h2(7) <= h2_reg(7) + h3_reg(7);
    h3(7) <= h3_reg(7);

    h0(6) <= h0_reg(6) xor h2_reg(6);
    h1(6) <= h1_reg(6);
    h2(6) <= h2_reg(6);
    h3(6) <= rotate_left(h3_reg(6), 34);

    -- h3 += h0;  h1 ^= h3;  h0 = Rot64(h0,5);
    h0(5) <= h0_reg(5);
    h1(5) <= h1_reg(5);
    h2(5) <= h2_reg(5);
    h3(5) <= h3_reg(5) + h0_reg(5);

    h0(4) <= rotate_left(h0_reg(4), 5);
    h1(4) <= h1_reg(4) xor h3_reg(4);
    h2(4) <= h2_reg(4);
    h3(4) <= h3_reg(4);

    -- h0 += h1;  h2 ^= h0;  h1 = Rot64(h1,36);
    h0(3) <= h0_reg(3) + h1_reg(3);
    h1(3) <= h1_reg(3);
    h2(3) <= h2_reg(3);
    h3(3) <= h3_reg(3);

    h0(2) <= h0_reg(2);
    h1(2) <= rotate_left(h1_reg(2), 36);
    h2(2) <= h2_reg(2) xor h0_reg(2);
    h3(2) <= h3_reg(2);

    -- h1 += h2;  h3 ^= h1;
    h0(1) <= h0_reg(1);
    h1(1) <= h1_reg(1) + h2_reg(1);
    h2(1) <= h2_reg(1);
    h3(1) <= h3_reg(1);

    h0(0) <= h0_reg(0);
    h1(0) <= h1_reg(0);
    h2(0) <= h2_reg(0);
    h3(0) <= h3_reg(0) xor h1_reg(0);

    -- ================================================
    --                    PIPELINE
    -- ================================================
    pipeline_g: for g in PIPE_LENGTH-1 downto 1 generate
        reg_g: if REG_SETUP(g) = '1' generate
            process (CLK)
            begin
                if rising_edge(CLK) then
                    key_reg(g-1) <= key_reg(g);
                    h0_reg(g-1)  <= h0(g);
                    h1_reg(g-1)  <= h1(g);
                    h2_reg(g-1)  <= h2(g);
                    h3_reg(g-1)  <= h3(g);
                    meta(g-1)    <= meta(g);
                    vld(g-1)     <= vld(g);

                    if (RESET = '1') then
                        vld(g-1) <= '0';
                    end if;
                end if;
            end process;
        else generate
            key_reg(g-1) <= key_reg(g);
            h0_reg(g-1)  <= h0(g);
            h1_reg(g-1)  <= h1(g);
            h2_reg(g-1)  <= h2(g);
            h3_reg(g-1)  <= h3(g);
            meta(g-1)    <= meta(g);
            vld(g-1)     <= vld(g);
        end generate;
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(0) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_KEY   <= key_reg(0);
                OUT_H0    <= h0(0);
                OUT_H1    <= h1(0);
                OUT_H2    <= h2(0);
                OUT_H3    <= h3(0);
                OUT_META  <= meta(0);
                OUT_VALID <= vld(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_KEY   <= key_reg(0);
        OUT_H0    <= h0(0);
        OUT_H1    <= h1(0);
        OUT_H2    <= h2(0);
        OUT_H3    <= h3(0);
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;

end architecture;
