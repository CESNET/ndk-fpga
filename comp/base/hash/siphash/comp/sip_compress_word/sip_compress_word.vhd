-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Subcomponent of the firmware implementation of the SIPHASH hash function
-- used to generate compression of a word.
--
-- The SIPROUND component is used.
--
-- The component is internally connected in this way for the normal version of the algorithm:
--
--                              +-------------------+
-- IN ---[V3 xor KEY(OFFSET)]---| SIPROUND * rounds |--+--[V0 xor KEY(OFFSET)]--+--- OUT
--                              +-------------------+  |                        |
--                                                     +-(if LAST)[V2 xor 0xFF]-+
--
-- For the extended version of the algorithm, 0xEE constant shall be used instead of 0xFF.
entity SIP_COMPRESS_WORD is
    generic (
        -- which 64-bit word of the key shall be processed.
        KEY_OFFSET         : natural := 0;
        -- width of the whole key.
        KEY_WIDTH          : natural := 312;
        -- width of the passthrough metadata.
        META_WIDTH         : natural := 32;
        -- number of SipRound rounds generate.
        ROUNDS             : natural := 2;
        -- width of the words and internal state variables. Use 64 for full SipHash and
        -- 32 for HalfSipHash.
        WORD_WIDTH         : natural := 64;
        -- if this word is the last one being compressed.
        FINAL_WORD         : boolean := false;
        -- constant that is to be xored with the final word (0xFF for normal variant and 0xEE for extended variant).
        FINAL_CONST        : natural := 255;
        -- setup of the registers of this components.
        REG_SETUP          : std_logic_vector
    );
    port (
        -- main clock
        CLK       : in  std_logic;
        -- synchronious reset
        RESET     : in  std_logic;
        -- key passthrough input
        IN_KEY    : in  unsigned(KEY_WIDTH-1 downto 0);
        -- internal state variables input
        IN_V0     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V1     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V2     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V3     : in  unsigned(WORD_WIDTH-1 downto 0);
        -- metadata input
        IN_META   : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID  : in  std_logic;

        -- key passthrough output
        OUT_KEY   : out unsigned(KEY_WIDTH-1 downto 0);
        -- internal state variables output
        OUT_V0    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V1    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V2    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V3    : out unsigned(WORD_WIDTH-1 downto 0);
        -- metadata output
        OUT_META  : out std_logic_vector(META_WIDTH-1 downto 0);
        -- valid passthrough
        OUT_VALID : out std_logic
    );
end entity;

architecture FULL of SIP_COMPRESS_WORD is
    -- length of the pipeline of this component
    constant PIPE_LENGTH : natural := ROUNDS + 3;

    -- logic
    signal v0            : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v1            : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v2            : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v3            : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);

    -- registers
    signal key           : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal vld           : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta          : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key(PIPE_LENGTH-1)  <= IN_KEY;
    vld(PIPE_LENGTH-1)  <= IN_VALID;
    meta(PIPE_LENGTH-1) <= IN_META;
    v0(PIPE_LENGTH-1)   <= IN_V0;
    v1(PIPE_LENGTH-1)   <= IN_V1;
    v2(PIPE_LENGTH-1)   <= IN_V2;
    -- v3 ^= m
    v3(PIPE_LENGTH-1)   <= IN_V3 xor IN_KEY((KEY_OFFSET + 1) * WORD_WIDTH - 1 downto KEY_OFFSET * WORD_WIDTH);

    -- ================================================
    --                     LOGIC
    -- ================================================
    -- compression rounds
    sipround_g: for g in PIPE_LENGTH-2 downto 2 generate
        compress_sipround_i: entity work.SIPROUND
        generic map (
            KEY_WIDTH  => KEY_WIDTH,
            META_WIDTH => META_WIDTH,
            WORD_WIDTH => WORD_WIDTH,
            REG_SETUP  => REG_SETUP(REG_SETUP'low + (g-1) * 4 downto REG_SETUP'low + (g-1) * 4 - 3)
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => key(g),
            IN_V0      => v0(g),
            IN_V1      => v1(g),
            IN_V2      => v2(g),
            IN_V3      => v3(g),
            IN_META    => meta(g),
            IN_VALID   => vld(g),
            OUT_KEY    => key(g-1),
            OUT_V0     => v0(g-1),
            OUT_V1     => v1(g-1),
            OUT_V2     => v2(g-1),
            OUT_V3     => v3(g-1),
            OUT_META   => meta(g-1),
            OUT_VALID  => vld(g-1)
        );
    end generate;
    -- v0 ^= m
    v0(0) <= v0(1) xor key(1)((KEY_OFFSET + 1) * WORD_WIDTH - 1 downto KEY_OFFSET * WORD_WIDTH);
    v1(0) <= v1(1);

    -- if remainder word v2 ^= 0xFF for normal and v2 ^= 0xEE for extended versions.
    last_g: if FINAL_WORD = true generate
        v2(0) <= v2(1) xor to_unsigned(FINAL_CONST, WORD_WIDTH);
    else generate
        v2(0) <= v2(1);
    end generate;

    v3(0) <= v3(1);

    -- propagating aux signals
    key(0)  <= key(1);
    meta(0) <= meta(1);
    vld(0)  <= vld(1);

    -- ================================================
    --                    PIPELINE
    -- ================================================
    end_reg_g: if REG_SETUP(REG_SETUP'low + REG_SETUP'length - 1) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                key(PIPE_LENGTH-2)  <= key(PIPE_LENGTH-1);
                meta(PIPE_LENGTH-2) <= meta(PIPE_LENGTH-1);
                vld(PIPE_LENGTH-2)  <= vld(PIPE_LENGTH-1);
                v0(PIPE_LENGTH-2)   <= v0(PIPE_LENGTH-1);
                v1(PIPE_LENGTH-2)   <= v1(PIPE_LENGTH-1);
                v2(PIPE_LENGTH-2)   <= v2(PIPE_LENGTH-1);
                v3(PIPE_LENGTH-2)   <= v3(PIPE_LENGTH-1);

                if (RESET = '1') then
                    vld(PIPE_LENGTH-2) <= '0';
                end if;
            end if;
        end process;
    else generate
        key(PIPE_LENGTH-2)  <= key(PIPE_LENGTH-1);
        meta(PIPE_LENGTH-2) <= meta(PIPE_LENGTH-1);
        vld(PIPE_LENGTH-2)  <= vld(PIPE_LENGTH-1);
        v0(PIPE_LENGTH-2)   <= v0(PIPE_LENGTH-1);
        v1(PIPE_LENGTH-2)   <= v1(PIPE_LENGTH-1);
        v2(PIPE_LENGTH-2)   <= v2(PIPE_LENGTH-1);
        v3(PIPE_LENGTH-2)   <= v3(PIPE_LENGTH-1);
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(REG_SETUP'low) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_KEY   <= key(0);
                OUT_V0    <= v0(0);
                OUT_V1    <= v1(0);
                OUT_V2    <= v2(0);
                OUT_V3    <= v3(0);
                OUT_META  <= meta(0);
                OUT_VALID <= vld(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_KEY   <= key(0);
        OUT_V0    <= v0(0);
        OUT_V1    <= v1(0);
        OUT_V2    <= v2(0);
        OUT_V3    <= v3(0);
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;
end architecture;
