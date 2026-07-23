-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.hash_pack.all;

-- Firmware implementation of the short version of the
-- SpookyHash hashing algorithm with a variable pipeline.
-- Supports keys up to 191B and generates hashes up to
-- 128b. Maximum possible frequency exceeds 700Mhz
-- for most key lengths, even 900Mhz for some.
--
-- For reference implementation in C++ see
-- https://burtleburtle.net/bob/hash/spooky.html
--
-- Spookyhash component consist of four individual components:
-- Sets32, Sets16, Remainder and Shortend. Sets32 and Sets16
-- are generated from the SPOOKY_SETS entity and specific variant
-- is chosen based on the SETS_TYPE generic. Additionally, Sets32
-- and Sets16 include the ShortMix component.
--
-- Components are connected in this way:
--       +------------+    +----------+    +-----------+    +----------+
-- IN----| n * Sets32 |----| ? Sets16 |----| Remainder |----| ShortEnd |----OUT
--       +------------+    +----------+    +-----------+    +----------+
--
-- The number of Sets32 and Sets16 components that are generated depends on the key
-- length. Sets32 components are used to process 32B chunks of the key.
-- The more 32B chunks there are, the more Sets32 components are generated.
-- A Sets16 component is generated if the Remainder of the key is greater than 15B.
-- Remainder and ShortEnd components are always generated.
entity SPOOKYHASH is
    generic (
        -- width of the input key, should not exceed 191B.
        -- If not aligned to whole bytes, the rest is
        -- extended by zeros
        KEY_WIDTH   : natural := 296;
        -- width of the generated hash, max 128 bits
        HASH_WIDTH  : natural := 128;
        -- width of the passthrough metadata
        META_WIDTH  : natural := 32;
        -- adds a register to the output
        OUT_REG     : boolean := true;

        -- Configuration of the pipeline. A value of '1' at a given index inserts a
        -- register, thus segmenting the logic path. Index 0 represents the output
        -- register, except for the REG_SETUP generic.
        -- Shorter paths between registers increase the maximum operating frequency
        -- (Fmax), but they also consume more resources and increase the initial latency.
        -- The synthesis tool may perform register re-timing.

        -- general register setup. The registers in the whole pipeline will be generated
        -- according to this repeating pattern.
        REG_SETUP   : std_logic_vector                              := "1";

        -- flag that general setting REG_SETUP should be overrided with specific
        -- component settings bellow.
        REG_SETUP_MANUAL_OVERRIDE : boolean                         := false;
        -- register setup of all generated SPOOKY_SETS components. If SETS_TYPE is set to
        -- false, most significant bit is ignored
        SETS_REG_SETUP            : std_logic_vector(27-1 downto 0) := "111111111111111111111111111";
        -- register setup of the SPOOKY_REMAINDER component
        REMAINDER_REG_SETUP       : std_logic_vector(1-1 downto 0)  := "1";
        -- register setup of the SPOOKY_SHORTEND component
        SHORTEND_REG_SETUP        : std_logic_vector(22-1 downto 0) := "1111111111111111111111"
    );
    port (
        -- main clock
        CLK         : in std_logic;
        -- synchronious reset
        RESET       : in std_logic;

        -- key to be hashed
        IN_KEY      : in std_logic_vector(KEY_WIDTH-1 downto 0);
        -- use seed for better durability of the hash
        IN_SEED     : in std_logic_vector(128-1 downto 0);
        -- passthrough metadata input
        IN_META     : in std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID    : in std_logic;

        -- calculated hash
        OUT_HASH    : out std_logic_vector(HASH_WIDTH-1 downto 0);
        -- passthrough metadata output
        OUT_META    : out std_logic_vector(META_WIDTH-1 downto 0);
        -- hash validity
        OUT_VALID   : out std_logic
    );
end entity;

architecture FULL of SPOOKYHASH is
    -- functions for calculating constants
    function f_calculate_remainder16 (remainder32: natural) return natural is
    begin
        if (remainder32 < 16) then
            return remainder32;
        else
            return remainder32 - 16;
        end if;
    end function;

    function f_calculate_remainder_cnt (remainder32: natural) return natural is
    begin
        if (remainder32 < 16) then
            return 3;
        else
            return 4;
        end if;
    end function;

    -- constant used in spookyhash algorithm
    constant SC_CONST            : unsigned(64-1 downto 0) := X"DEADBEEFDEADBEEF";
    -- width of key aligned to bytes
    constant KEY_WIDTH_ALIGNED   : natural := div_roundup(KEY_WIDTH, 8) * 8;
    -- whole remainder (0 - 31)
    constant REMAINDER32         : natural := (KEY_WIDTH_ALIGNED / 8) mod 32;
    -- small remainder (0 - 15)
    constant REMAINDER16         : natural := f_calculate_remainder16(REMAINDER32);
    -- number of Sets32 components
    constant SETS32_CNT          : natural := KEY_WIDTH_ALIGNED / 256;
    -- number of registers processing remainder of the key
    constant REMAINDER_CNT       : natural := f_calculate_remainder_cnt(REMAINDER32);
    -- number of Sets16 components (REMAINDER_CNT=3 => 0; REMAINDER_CNT=4 => 1)
    constant SETS16_CNT          : natural := REMAINDER_CNT / 4;
    -- length of the pipeline of this component
    constant PIPE_LENGTH         : natural := SETS32_CNT + REMAINDER_CNT;
    -- lsb of remainder processed by Sets16
    constant SETS16_LOW          : natural := SETS32_CNT * 256;
    -- msb of remainder processed by Sets16 (and lsb processed by Remainder component)
    constant SETS16_HIGH         : natural := SETS16_LOW + ((REMAINDER32 - REMAINDER16) * 8);
    -- msb of remainder processed by the Remainder component
    constant SETS15_HIGH         : natural := SETS16_LOW + (REMAINDER32 * 8);
    -- chosen register setup for the sets components (including Sets16)
    constant REG_SETUP_SETS      : slv_array_t(SETS32_CNT + SETS16_CNT - 1 downto 0)(SETS_REG_SETUP'high downto 0) := f_get_reg_setup(SETS32_CNT + SETS16_CNT, SETS_REG_SETUP'length, 0, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, SETS_REG_SETUP);
    -- chosen register setup for the Remainder components
    constant REG_SETUP_REMAINDER : std_logic_vector(REMAINDER_REG_SETUP'high downto 0) := slv_array_ser(f_get_reg_setup(1, REMAINDER_REG_SETUP'length, (SETS32_CNT + SETS16_CNT) * SETS_REG_SETUP'length, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, REMAINDER_REG_SETUP));
    -- chosen register setup for the ShortEnd components
    constant REG_SETUP_SHORTEND  : std_logic_vector(SHORTEND_REG_SETUP'high downto 0) := slv_array_ser(f_get_reg_setup(1, SHORTEND_REG_SETUP'length, (SETS32_CNT + SETS16_CNT) * SETS_REG_SETUP'length + REMAINDER_REG_SETUP'length, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, SHORTEND_REG_SETUP));

    signal key  : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH_ALIGNED-1 downto 0);
    signal h0   : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1   : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2   : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3   : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal meta : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    signal vld  : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal hash : std_logic_vector(128-1 downto 0);

begin
    assert HASH_WIDTH <= 128
        report "Maximum supported HASH_WIDTH is 128b."
        severity error;

    assert KEY_WIDTH <= 1528
        report "KEY_WIDTH should not be greater than 191B."
        severity warning;

    -- ================================================
    --                      INPUT
    -- ================================================
    align_key_g: if KEY_WIDTH mod 8 = 0 generate
        key(PIPE_LENGTH-1) <= unsigned(IN_KEY);
    else generate
        key(PIPE_LENGTH-1) <= (8-(KEY_WIDTH mod 8)-1 downto 0 => '0') & unsigned(IN_KEY);
    end generate;

    h0(PIPE_LENGTH-1) <= unsigned(IN_SEED(64-1 downto 0));
    h1(PIPE_LENGTH-1) <= unsigned(IN_SEED(128-1 downto 64));

    h2(PIPE_LENGTH-1)   <= SC_CONST;
    h3(PIPE_LENGTH-1)   <= SC_CONST;
    meta(PIPE_LENGTH-1) <= IN_META;
    vld(PIPE_LENGTH-1)  <= IN_VALID;

    -- ================================================
    --                     LOGIC
    -- ================================================
    -- handle all complete sets of 32 bytes
    sets32_g: for g in PIPE_LENGTH-1 downto REMAINDER_CNT generate
        sets32_i: entity work.SPOOKY_SETS
        generic map (
            SETS_TYPE  => true,
            KEY_WIDTH  => KEY_WIDTH_ALIGNED,
            META_WIDTH => META_WIDTH,
            KEY_OFFSET => (PIPE_LENGTH - g - 1) * 256,
            REG_SETUP  => REG_SETUP_SETS(PIPE_LENGTH - g - 1)
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => key(g),
            IN_H0      => h0(g),
            IN_H1      => h1(g),
            IN_H2      => h2(g),
            IN_H3      => h3(g),
            IN_META    => meta(g),
            IN_VALID   => vld(g),
            OUT_KEY    => key(g-1),
            OUT_H0     => h0(g-1),
            OUT_H1     => h1(g-1),
            OUT_H2     => h2(g-1),
            OUT_H3     => h3(g-1),
            OUT_META   => meta(g-1),
            OUT_VALID  => vld(g-1)
        );
    end generate;

    -- handle the case of 16+ remaining bytes
    sets16_g: if REMAINDER32 >= 16 generate
        sets16_i: entity work.SPOOKY_SETS
        generic map (
            SETS_TYPE  => false,
            KEY_WIDTH  => KEY_WIDTH_ALIGNED,
            META_WIDTH => META_WIDTH,
            KEY_OFFSET => SETS16_LOW,
            REG_SETUP  => REG_SETUP_SETS(SETS32_CNT)
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => key(3),
            IN_H0      => h0(3),
            IN_H1      => h1(3),
            IN_H2      => h2(3),
            IN_H3      => h3(3),
            IN_META    => meta(3),
            IN_VALID   => vld(3),
            OUT_KEY    => key(2),
            OUT_H0     => h0(2),
            OUT_H1     => h1(2),
            OUT_H2     => h2(2),
            OUT_H3     => h3(2),
            OUT_META   => meta(2),
            OUT_VALID  => vld(2)
        );
    end generate;

    -- handle the last 0..15 bytes, and its length
    remainder_i: entity work.SPOOKY_REMAINDER
    generic map (
        KEY_WIDTH  => KEY_WIDTH_ALIGNED,
        REMAINDER  => REMAINDER16,
        SC_CONST   => SC_CONST,
        META_WIDTH => META_WIDTH,
        OUT_REG    => (REG_SETUP_REMAINDER(0) = '1')
    ) port map (
        CLK       => CLK,
        RESET     => RESET,
        IN_KEY    => key(2)(SETS15_HIGH-1 downto SETS16_HIGH),
        IN_H0     => h0(2),
        IN_H1     => h1(2),
        IN_H2     => h2(2),
        IN_H3     => h3(2),
        IN_META   => meta(2),
        IN_VALID  => vld(2),
        OUT_H0    => h0(1),
        OUT_H1    => h1(1),
        OUT_H2    => h2(1),
        OUT_H3    => h3(1),
        OUT_META  => meta(1),
        OUT_VALID => vld(1)
    );

    short_end_i: entity work.SPOOKY_SHORTEND
    generic map (
        META_WIDTH => META_WIDTH,
        REG_SETUP  => REG_SETUP_SHORTEND
    ) port map (
        CLK       => CLK,
        RESET     => RESET,
        IN_H0     => h0(1),
        IN_H1     => h1(1),
        IN_H2     => h2(1),
        IN_H3     => h3(1),
        IN_META   => meta(1),
        IN_VALID  => vld(1),
        OUT_H0    => h0(0),
        OUT_H1    => h1(0),
        OUT_H2    => h2(0),
        OUT_H3    => h3(0),
        OUT_META  => meta(0),
        OUT_VALID => vld(0)
    );

    hash <= std_logic_vector(h1(0)) & std_logic_vector(h0(0));

    -- ================================================
    --                     OUTPUT
    -- ================================================
    output_reg: if OUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_HASH  <= hash(HASH_WIDTH-1 downto 0);
                OUT_META  <= meta(0);
                OUT_VALID <= vld(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_HASH  <= hash(HASH_WIDTH-1 downto 0);
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;
end architecture;
