-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.hash_pack.all;

-- Firmware implementation of chaskey cryptographic hash function
-- using variable pipeline intended for use in high speed networking
-- applications.
--
-- Chaskey is a light-weigth cryptographic hash function based on
-- ARX (Addition, Rotations, XOR) operations. The four state variables
-- are 32-bit and generated hash is 128-bits in length.
--
-- The strength of the hash function in terms of security
-- can be configured by setting the ROUNDS generic, which
-- indicates how many ARX permutations per block of the
-- key will be generated. Typical settings are 8 and 16,
-- the version with 16 rounds is also refered to as Chaskey-LTS.
--
-- The CHASKEY entity consists of two components - CHASKEY_PROCESS_BLOCK
-- and CHASKEY_REMAINDER. Pipelines of both of these components can be
-- configured using their coresponding generics.
--
-- The components are arranged in the following manner:
--
--                   INPUT                            KEY BLOCK PROCESSING              REMAINDER PROCESSING                 HASH
--                                       +------------------------------------------+   +-------------------+
-- IN ---[V(3:0)(31:0) := SEED(127:0)]---| CHASKEY_PROCESS_BLOCK * (word_count - 1) |---| CHASKEY_REMAINDER |---[HASH(127:0) := V(3:0)(31:0)]--- OUT
--                                       +------------------------------------------+   +-------------------+
--
-- Maximum possible frequency when the pipeline is fully registered
-- exceeds 800 MHz for most configurations and reaches 1 Ghz for some.
--
-- For specification and reference C++ implementation see:
--     Specification : https://eprint.iacr.org/2014/386.pdf
--     C++           : https://gitlab.com/fwojcik/smhasher3/-/blob/main/hashes/chaskey.cpp
--
entity CHASKEY is
    generic (
        -- width of the input key.
        -- If not aligned to whole bytes, the rest is extended by zeros.
        KEY_WIDTH                 : natural := 312;
        -- width of the generated hash, max 128 bits.
        HASH_WIDTH                : natural := 128;
        -- width of the passthrough metadata.
        META_WIDTH                : natural := 32;
        -- number of permutation rounds. Typical settings are 8 and 16 (Chaskey-LTS).
        -- More rounds results in better security.
        ROUNDS                    : natural := 8;
        -- adds a register to the output.
        OUT_REG                   : boolean := true;

        -- Configuration of the pipeline. A value of '1' at a given index inserts a
        -- register, thus segmenting the logic path. Index 0 always represents the
        -- output register.
        -- Shorter paths between registers increase the maximum operating frequency
        -- (Fmax), but they also consume more resources and increase the initial latency.
        -- The synthesis tool may perform register re-timing.

        -- general register setup. The registers in the whole pipeline will be generated
        -- according to this repeating patern.
        REG_SETUP                 : std_logic_vector                := "1";

        -- flag that general setting REG_SETUP should be overrided with specific
        -- component setting bellow.
        REG_SETUP_MANUAL_OVERRIDE : boolean                         := false;
        -- setup of the registers of CHASKEY_ROUND components.
        ROUND_REG_SETUP           : std_logic_vector(4-1 downto 0)  := "1111";
        -- adds a register to the start of the CHASKEY_PROCESS_BLOCK component.
        PROCESS_BLOCK_START_REG   : std_logic_vector(1-1 downto 0)  := "1";
        -- setup of the registers of the CHASKEY_REMAINDER component. The
        -- bit at index 3 is used only when the key is not aligned
        -- (is not a multiple of 128).
        REMAINDER_REG_SETUP       : std_logic_vector(4-1 downto 0)  := "1111"
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

architecture FULL of CHASKEY is
    -- width of the key aligned to whole bytes.
    constant KEY_WIDTH_BYTE_ALIGNED     : natural := div_roundup(KEY_WIDTH, 8) * 8;
    -- width of the words and state variables.
    constant WORD_WIDTH                 : natural := 32;
    -- width of a block of a key.
    constant BLOCK_WIDTH                : natural := WORD_WIDTH * 4;
    -- width of the key aligned to whole words and extended by a extra word.
    constant KEY_WIDTH_BLOCK_ALIGNED    : natural := div_roundup(KEY_WIDTH, BLOCK_WIDTH) * BLOCK_WIDTH;
    -- number of components processing key blocks to be generated.
    constant PROCESS_BLOCK_COUNT        : natural := (KEY_WIDTH_BLOCK_ALIGNED / BLOCK_WIDTH) - 1;
    -- number of remaining bytes.
    constant REMAIN                     : natural := (KEY_WIDTH_BYTE_ALIGNED / 8) mod (BLOCK_WIDTH / 8);
    -- length of the pipeline of this component.
    constant PIPE_LENGTH                : natural := PROCESS_BLOCK_COUNT + 2;
    -- joined setup of the registers of the CHASKEY_COMPRESS_BLOCK component
    constant COMPRESS_BLOCK_REG_SETUP   : std_logic_vector(ROUND_REG_SETUP'length * ROUNDS downto 0) := PROCESS_BLOCK_START_REG & f_duplicate_std_logic_vector(ROUND_REG_SETUP, ROUNDS);
    -- joined setup of the registers of the CHASKEY_REMAINDER component
    constant REMAINDER_JOINED_REG_SETUP : std_logic_vector((ROUND_REG_SETUP'length * ROUNDS) + REMAINDER_REG_SETUP'length - 1 downto 0) := REMAINDER_REG_SETUP(4-1 downto 1) & f_duplicate_std_logic_vector(ROUND_REG_SETUP, ROUNDS) & REMAINDER_REG_SETUP(0);
    -- actual setup of the pipeline of the individual CHASKEY_PROCESS_BLOCK components.
    constant REG_SETUP_COMPRESSION      : slv_array_t(PROCESS_BLOCK_COUNT-1 downto 0)(COMPRESS_BLOCK_REG_SETUP'length-1 downto 0) := f_get_reg_setup(PROCESS_BLOCK_COUNT, COMPRESS_BLOCK_REG_SETUP'length, 0, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, COMPRESS_BLOCK_REG_SETUP);
    -- actual setup of the pipeline of the CHASKEY_REMAINDER component
    constant REG_SETUP_REMAINDER        : std_logic_vector(REMAINDER_JOINED_REG_SETUP'length-1 downto 0) := slv_array_ser(f_get_reg_setup(1, REMAINDER_JOINED_REG_SETUP'length, PROCESS_BLOCK_COUNT * COMPRESS_BLOCK_REG_SETUP'length, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, REMAINDER_JOINED_REG_SETUP));


    signal key  : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH_BLOCK_ALIGNED-1 downto 0);
    signal seed : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    signal v0   : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v1   : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v2   : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v3   : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal meta : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    signal vld  : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal hash : std_logic_vector(128-1 downto 0);

begin
    assert HASH_WIDTH <= 128
        report "HASH_WIDTH must not be greater than 128 bits."
        severity error;

    -- ================================================
    --                      INPUT
    -- ================================================
    key(PIPE_LENGTH-1)(KEY_WIDTH_BYTE_ALIGNED-1 downto 0) <= (KEY_WIDTH_BYTE_ALIGNED-KEY_WIDTH-1 downto 0 => '0') & unsigned(IN_KEY);

    -- add padding bit to the key if it's not alligned
    remain_const_g: if REMAIN > 0 generate
        key(PIPE_LENGTH-1)(KEY_WIDTH_BLOCK_ALIGNED-1 downto KEY_WIDTH_BYTE_ALIGNED) <= (KEY_WIDTH_BLOCK_ALIGNED-KEY_WIDTH_BYTE_ALIGNED-1 downto 1 => '0') & "1";
    end generate;

    -- use seed as base for state variables
    v0(PIPE_LENGTH-1)   <= unsigned(IN_SEED( 32-1 downto  0));
    v1(PIPE_LENGTH-1)   <= unsigned(IN_SEED( 64-1 downto 32));
    v2(PIPE_LENGTH-1)   <= unsigned(IN_SEED( 96-1 downto 64));
    v3(PIPE_LENGTH-1)   <= unsigned(IN_SEED(128-1 downto 96));

    seed(PIPE_LENGTH-1) <= unsigned(IN_SEED);
    meta(PIPE_LENGTH-1) <= IN_META;
    vld(PIPE_LENGTH-1)  <= IN_VALID;

    -- ================================================
    --                     LOGIC
    -- ================================================

    -- processing of 128-bit blocks of the key
    process_blocks_g: for g in PIPE_LENGTH-1 downto 2 generate
        process_block_i: entity work.CHASKEY_PROCESS_BLOCK
        generic map (
            KEY_OFFSET      => PIPE_LENGTH - g - 1,
            KEY_WIDTH       => KEY_WIDTH_BLOCK_ALIGNED,
            META_WIDTH      => META_WIDTH,
            ROUNDS          => ROUNDS,
            REG_SETUP       => REG_SETUP_COMPRESSION(PIPE_LENGTH - g - 1)
        ) port map (
            CLK             => CLK,
            RESET           => RESET,
            IN_KEY          => key(g),
            IN_SEED         => seed(g),
            IN_V0           => v0(g),
            IN_V1           => v1(g),
            IN_V2           => v2(g),
            IN_V3           => v3(g),
            IN_META         => meta(g),
            IN_VALID        => vld(g),
            OUT_KEY         => key(g-1),
            OUT_SEED        => seed(g-1),
            OUT_V0          => v0(g-1),
            OUT_V1          => v1(g-1),
            OUT_V2          => v2(g-1),
            OUT_V3          => v3(g-1),
            OUT_META        => meta(g-1),
            OUT_VALID       => vld(g-1)
        );
    end generate;

    -- processing the remainder of the key
    remainder_i: entity work.CHASKEY_REMAINDER
    generic map (
        META_WIDTH      => META_WIDTH,
        ROUNDS          => ROUNDS,
        REMAIN          => REMAIN,
        REG_SETUP       => REG_SETUP_REMAINDER
    ) port map (
        CLK             => CLK,
        RESET           => RESET,
        IN_KEY          => key(1)(KEY_WIDTH_BLOCK_ALIGNED-1 downto KEY_WIDTH_BLOCK_ALIGNED - BLOCK_WIDTH),
        IN_SEED         => seed(1),
        IN_V0           => v0(1),
        IN_V1           => v1(1),
        IN_V2           => v2(1),
        IN_V3           => v3(1),
        IN_META         => meta(1),
        IN_VALID        => vld(1),
        OUT_V0          => v0(0),
        OUT_V1          => v1(0),
        OUT_V2          => v2(0),
        OUT_V3          => v3(0),
        OUT_META        => meta(0),
        OUT_VALID       => vld(0)
    );

    -- concating state variables to create resulting hash
    hash <= std_logic_vector(v3(0)) & std_logic_vector(v2(0)) & std_logic_vector(v1(0)) & std_logic_vector(v0(0));

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
