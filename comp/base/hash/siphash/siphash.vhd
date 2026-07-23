-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.hash_pack.all;

-- Firmware implementation of SipHash cryptographic hash function
-- using variable pipeline intended for use in high speed networking
-- applications.
--
-- Includes SipHash and HalfSipHash variants, use the WORD_WIDTH
-- generics to switch between these two. SipHash offers better
-- cryptographic strength but consumes more resources, HalfSipHash
-- is cryptographically weaker but consumes less resources.
--
-- Also includes standard and extended versions. Normal versions
-- generate hash up to 64b for SipHash and 32b for HalfSipHash,
-- extended versions up to 128b for SipHash and 64b for HalfSipHash.
-- Since more finalization rounds are generated, extended versions
-- consume higher resources.
--
-- Number of comperession and finalization rounds can be configured.
-- Standard versions are SipHash-2-4, which offers balance between
-- cryptographic strength and consumed resources, and SipHash-4-8,
-- which offers higher cryptographic strength for the price of higher
-- resource consumption.
--
-- SIPHASH component consists of the SIPROUND and SIP_COMPRESS_WORD
-- subcomponents. Pipelines of both of these components can be
-- configured using their coresponding generics.
--
-- The components are connected in this manner for normal version of siphash:
--
--             INPUT                     COMPRESSION                          FINALIZATION                      HASH
--                            +--------------------------------+   +--------------------------------+
-- IN ---[SEED xor V_CONST]---| SIP_COMPRESS_WORD * word_count |---| SIPROUND * finalization_rounds |---[v0 ^ v1 ^ v2 ^ v3]--- OUT
--                            +--------------------------------+   +--------------------------------+
--
-- The extended verion then adds between FINALIZATION and HASH the following:
--
--                             FINALIZATION_EXT
--                                 +--------------------------------+
-- FINALIZATION ---[V1 XOR 0xDD]---| SIPROUND * finalization_rounds |--- HASH
--                                 +--------------------------------+
--
-- In the case of HalfSipHash, the HASH changes to [v1 ^ v3].
--
-- For specification, reference C and Python implementation, see:
--     Specification : https://cr.yp.to/siphash/siphash-20120918.pdf
--     C             : https://github.com/veorq/SipHash
--     Python        : https://pypi.org/project/siphash/
entity SIPHASH is
    generic (
        -- width of the input key.
        -- If not aligned to whole bytes, the rest is extended by zeros.
        KEY_WIDTH           : natural := 296;
        -- width of the generated hash, max 128 bits.
        HASH_WIDTH          : natural := 128;
        -- width of the passthrough metadata.
        META_WIDTH          : natural := 32;
        -- number of compression rounds.
        COMPRESSION_ROUNDS  : natural := 2;
        -- number of finalization rounds.
        FINALIZATION_ROUNDS : natural := 4;
        -- width of the words and internal state variables. Use 64 for full SipHash and
        -- 32 for HalfSipHash
        WORD_WIDTH          : natural := 64;
        -- adds a register to the output.
        OUT_REG             : boolean := true;

        -- Configuration of the pipeline. A value of '1' at a given index inserts a
        -- register, thus segmenting the logic path. Index 0 always represents the
        -- output register.
        -- Shorter paths between registers increase the maximum operating frequency
        -- (Fmax), but they also consume more resources and increase the initial latency.
        -- The synthesis tool may perform register re-timing.

        -- general register setup. The registers in the whole pipeline will be generated
        -- according to this repeating pattern.
        REG_SETUP   : std_logic_vector                              := "1";

        -- flag that general setting REG_SETUP should be overrided with specific
        -- component setting bellow.
        REG_SETUP_MANUAL_OVERRIDE   : boolean                          := false;
        -- manual setting of the pipeline of the SIPROUND component.
        SIPROUND_REG_SETUP          : std_logic_vector(4-1 downto 0) := "1111";
        -- manual setting of the SIP_COMPRESS_WORD component.
        SIP_COMPRESS_WORD_REG_SETUP : std_logic_vector(2-1 downto 0) := "11";
        -- if 128 bit variant of the algorithm is used, adds a register to the
        -- start of the second finalization round.
        HASH_EXTENSION_START_REG    : std_logic_vector(1-1 downto 0) := "1"
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

architecture FULL of SIPHASH is
    -- the length of the array of the hash signal is different for the normal and extended versions.
    function f_get_hash_pipe_length (hash_width: natural; word_width: natural; fin_rounds: natural) return natural is
    begin
        if (hash_width > word_width) then
            return fin_rounds + 2;
        else
            return 1;
        end if;
    end function;

    -- the constant xored with the remainder of the key is different for the normal and extended versions.
    function f_get_final_const (hash_width: natural; word_width: natural) return natural is
    begin
        if (hash_width > word_width) then
            return 238;
        else
            return 255;
        end if;
    end function;

    -- the constants xored with the seed are different for 32 bit and 64 bit versions and
    -- normal and extended versions.
    function f_get_v_constants (hash_width: natural; word_width: natural) return u_array_t is
        variable v_const : u_array_t(4-1 downto 0)(word_width-1 downto 0);
    begin
        case word_width is
            when 32 =>
                v_const(0) := (others => '0');

                if (hash_width > word_width) then
                    v_const(1) := X"000000EE";
                else
                    v_const(1) := (others => '0');
                end if;

                v_const(2) := X"6C796765";
                v_const(3) := X"74656462";
            when 64 =>
                v_const(0) := X"736F6D6570736575";

                if (hash_width > word_width) then
                    v_const(1) := X"646F72616E646F6D" xor X"00000000000000EE";
                else
                    v_const(1) := X"646F72616E646F6D";
                end if;

                v_const(2) := X"6C7967656E657261";
                v_const(3) := X"7465646279746573";
            when others => null;
        end case;

        return v_const;
    end function;

    -- width of the key aligned to whole bytes
    constant KEY_WIDTH_BYTE_ALIGNED  : natural := div_roundup(KEY_WIDTH, 8) * 8;
    -- word width in bytes
    constant WORD_WIDTH_BYTES        : natural := WORD_WIDTH / 8;
    -- number of words
    constant WORD_COUNT              : natural := KEY_WIDTH_BYTE_ALIGNED / WORD_WIDTH;
    -- width of the key aligned to whole words and extended by a extra word
    constant KEY_WIDTH_WORD_ALIGNED  : natural := (WORD_COUNT * WORD_WIDTH) + WORD_WIDTH;
    -- number of remaining bytes
    constant REMAINDER_BYTES         : natural := (KEY_WIDTH_BYTE_ALIGNED / 8) - (WORD_COUNT * WORD_WIDTH_BYTES);
    -- padding of remaining bytes
    constant PADDING                 : unsigned(WORD_WIDTH-1 downto 0) := shift_left(to_unsigned(WORD_COUNT * WORD_WIDTH_BYTES + REMAINDER_BYTES, WORD_WIDTH) and to_unsigned(255, WORD_WIDTH), WORD_WIDTH-8);
    -- the constants xored with the seed generating v0, v1, v2 and v3
    constant V_CONST                 : u_array_t(4-1 downto 0)(WORD_WIDTH-1 downto 0) := f_get_v_constants(HASH_WIDTH, WORD_WIDTH);
    -- length of the hash array
    constant HASH_PIPE_LENGTH        : natural := f_get_hash_pipe_length(HASH_WIDTH, WORD_WIDTH, FINALIZATION_ROUNDS);
    -- length of the pipeline of this component
    constant PIPE_LENGTH             : natural := WORD_COUNT + FINALIZATION_ROUNDS + HASH_PIPE_LENGTH + 1;
    -- = sip compress pipeline length
    constant SCPL                    : natural := (SIPROUND_REG_SETUP'length * COMPRESSION_ROUNDS) + SIP_COMPRESS_WORD_REG_SETUP'length;
    -- joins reg setup of sipround and operation with message before and after sipround.
    constant SIP_COMPRESS_JOINED_RS  : std_logic_vector(SCPL-1 downto 0) := SIP_COMPRESS_WORD_REG_SETUP(1) & f_duplicate_std_logic_vector(SIPROUND_REG_SETUP, COMPRESSION_ROUNDS) & SIP_COMPRESS_WORD_REG_SETUP(0);
    -- actual setup of the pipeline of the individual SIP_COMPRESS_WORD components.
    constant REG_SETUP_SIP_COMPRESS  : slv_array_t(WORD_COUNT downto 0)(SCPL-1 downto 0) := f_get_reg_setup(WORD_COUNT + 1, SCPL, 0, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, SIP_COMPRESS_JOINED_RS);
    -- actual setup of the pipeline of the individual SIPROUND components in the finalization.
    constant REG_SETUP_FINALIZATION  : slv_array_t(FINALIZATION_ROUNDS-1 downto 0)(SIPROUND_REG_SETUP'high downto 0) := f_get_reg_setup(FINALIZATION_ROUNDS, SIPROUND_REG_SETUP'length, WORD_COUNT * SCPL, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, SIPROUND_REG_SETUP);
    -- if register will be added after the generation of lower half of the hash in case of extended components.
    constant REG_SETUP_EXT_START_REG : std_logic := slv_array_ser(f_get_reg_setup(1, 1, (WORD_COUNT * SCPL) + (FINALIZATION_ROUNDS * SIPROUND_REG_SETUP'length), REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, HASH_EXTENSION_START_REG))(0);
    -- actual setup of the pipeline of the extended finalization.
    constant REG_SETUP_EXT_FINAL     : slv_array_t(FINALIZATION_ROUNDS-1 downto 0)(SIPROUND_REG_SETUP'high downto 0) := f_get_reg_setup(FINALIZATION_ROUNDS, SIPROUND_REG_SETUP'length, (WORD_COUNT * SCPL) + (FINALIZATION_ROUNDS * SIPROUND_REG_SETUP'length) + 1, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, SIPROUND_REG_SETUP);

    -- logic
    signal key                       : u_array_t(PIPE_LENGTH-1 downto PIPE_LENGTH - WORD_COUNT - 2)(KEY_WIDTH_WORD_ALIGNED-1 downto 0);
    signal v0                        : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v1                        : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v2                        : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v3                        : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal meta                      : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    signal vld                       : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal hash                      : u_array_t(HASH_PIPE_LENGTH-1 downto 0)((WORD_WIDTH*2)-1 downto 0);

    -- registers
    signal v0_hesr                   : unsigned(WORD_WIDTH-1 downto 0);
    signal v1_hesr                   : unsigned(WORD_WIDTH-1 downto 0);
    signal v2_hesr                   : unsigned(WORD_WIDTH-1 downto 0);
    signal v3_hesr                   : unsigned(WORD_WIDTH-1 downto 0);
    signal meta_hesr                 : std_logic_vector(META_WIDTH-1 downto 0);
    signal vld_hesr                  : std_logic;
    signal hash_hesr                 : unsigned(WORD_WIDTH-1 downto 0);

begin
    assert WORD_WIDTH = 32 or WORD_WIDTH = 64
        report "Supported values of WORD_WIDTH are 32 (halfsiphash) and 64 (siphash)."
        severity error;

    assert HASH_WIDTH <= 2 * WORD_WIDTH
        report "HASH_WIDTH must not be greater than WORD_WIDTH * 2."
        severity error;

    -- ================================================
    --                      INPUT
    -- ================================================
    key(PIPE_LENGTH-1)(WORD_COUNT*WORD_WIDTH-1 downto 0)                      <= unsigned(IN_KEY(WORD_COUNT*WORD_WIDTH-1 downto 0));
    key(PIPE_LENGTH-1)(KEY_WIDTH_WORD_ALIGNED-1 downto WORD_COUNT*WORD_WIDTH) <= ((KEY_WIDTH_WORD_ALIGNED - KEY_WIDTH - 1 downto 0 => '0') & unsigned(IN_KEY(KEY_WIDTH-1 downto WORD_COUNT*WORD_WIDTH))) or PADDING;

    v0(PIPE_LENGTH-1)   <= V_CONST(0) xor unsigned(IN_SEED(WORD_WIDTH-1 downto 0));
    v1(PIPE_LENGTH-1)   <= V_CONST(1) xor unsigned(IN_SEED((WORD_WIDTH*2)-1 downto WORD_WIDTH));
    v2(PIPE_LENGTH-1)   <= V_CONST(2) xor unsigned(IN_SEED(WORD_WIDTH-1 downto 0));
    v3(PIPE_LENGTH-1)   <= V_CONST(3) xor unsigned(IN_SEED((WORD_WIDTH*2)-1 downto WORD_WIDTH));

    meta(PIPE_LENGTH-1) <= IN_META;
    vld(PIPE_LENGTH-1)  <= IN_VALID;

    -- ================================================
    --                     LOGIC
    -- ================================================
    -- compression
    compression_pipeline_g: for g in PIPE_LENGTH-1 downto FINALIZATION_ROUNDS + HASH_PIPE_LENGTH generate
        sip_compress_word_i: entity work.SIP_COMPRESS_WORD
        generic map (
            KEY_OFFSET         => PIPE_LENGTH - g - 1,
            KEY_WIDTH          => KEY_WIDTH_WORD_ALIGNED,
            META_WIDTH         => META_WIDTH,
            ROUNDS             => COMPRESSION_ROUNDS,
            WORD_WIDTH         => WORD_WIDTH,
            FINAL_WORD         => PIPE_LENGTH - g - 1 = WORD_COUNT,
            FINAL_CONST        => f_get_final_const(HASH_WIDTH, WORD_WIDTH),
            REG_SETUP          => REG_SETUP_SIP_COMPRESS(PIPE_LENGTH - g - 1)
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

    -- finalization
    finalization_g: for g in FINALIZATION_ROUNDS + HASH_PIPE_LENGTH - 1 downto HASH_PIPE_LENGTH generate
        final_sipround_i: entity work.SIPROUND
        generic map (
            KEY_WIDTH  => KEY_WIDTH_WORD_ALIGNED,
            META_WIDTH => META_WIDTH,
            WORD_WIDTH => WORD_WIDTH,
            REG_SETUP  => REG_SETUP_FINALIZATION(FINALIZATION_ROUNDS + HASH_PIPE_LENGTH - g - 1)
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => (others => '0'),
            IN_V0      => v0(g),
            IN_V1      => v1(g),
            IN_V2      => v2(g),
            IN_V3      => v3(g),
            IN_META    => meta(g),
            IN_VALID   => vld(g),
            OUT_V0     => v0(g-1),
            OUT_V1     => v1(g-1),
            OUT_V2     => v2(g-1),
            OUT_V3     => v3(g-1),
            OUT_META   => meta(g-1),
            OUT_VALID  => vld(g-1)
        );
    end generate;

    -- generating more finalization rounds for the extended version of the algorithm.
    hash_extension_g: if HASH_WIDTH > WORD_WIDTH generate

        -- generating hash differently for SipHash and HalfSipHash.
        lower_hash_g: if WORD_WIDTH = 64 generate
            hash(HASH_PIPE_LENGTH-1)(WORD_WIDTH-1 downto 0) <= v0(HASH_PIPE_LENGTH-1) xor v1(HASH_PIPE_LENGTH-1) xor v2(HASH_PIPE_LENGTH-1) xor v3(HASH_PIPE_LENGTH-1);
        else generate
            hash(HASH_PIPE_LENGTH-1)(WORD_WIDTH-1 downto 0) <= v1(HASH_PIPE_LENGTH-1) xor v3(HASH_PIPE_LENGTH-1);
        end generate;

        -- xoring v1 with 0xDD constant.
        v0(HASH_PIPE_LENGTH-2)                          <= v0_hesr;
        v1(HASH_PIPE_LENGTH-2)                          <= v1_hesr xor to_unsigned(221, WORD_WIDTH);
        v2(HASH_PIPE_LENGTH-2)                          <= v2_hesr;
        v3(HASH_PIPE_LENGTH-2)                          <= v3_hesr;
        meta(HASH_PIPE_LENGTH-2)                        <= meta_hesr;
        vld(HASH_PIPE_LENGTH-2)                         <= vld_hesr;
        hash(HASH_PIPE_LENGTH-2)(WORD_WIDTH-1 downto 0) <= hash_hesr;

        -- generating more finalization rounds.
        hash_extension_rounds_g: for g in HASH_PIPE_LENGTH-2 downto 1 generate
            hash_extension_sipround_i: entity work.SIPROUND
            generic map (
                KEY_WIDTH  => WORD_WIDTH,
                META_WIDTH => META_WIDTH,
                WORD_WIDTH => WORD_WIDTH,
                REG_SETUP  => REG_SETUP_EXT_FINAL(HASH_PIPE_LENGTH - g - 2)
            ) port map (
                CLK        => CLK,
                RESET      => RESET,
                IN_KEY     => hash(g)(WORD_WIDTH-1 downto 0),
                IN_V0      => v0(g),
                IN_V1      => v1(g),
                IN_V2      => v2(g),
                IN_V3      => v3(g),
                IN_META    => meta(g),
                IN_VALID   => vld(g),
                OUT_KEY    => hash(g-1)(WORD_WIDTH-1 downto 0),
                OUT_V0     => v0(g-1),
                OUT_V1     => v1(g-1),
                OUT_V2     => v2(g-1),
                OUT_V3     => v3(g-1),
                OUT_META   => meta(g-1),
                OUT_VALID  => vld(g-1)
            );
        end generate;

        -- generating hash differently for SipHash and HalfSipHash
        upper_hash_g: if WORD_WIDTH = 64 generate
            hash(0)((WORD_WIDTH*2)-1 downto WORD_WIDTH) <= v0(0) xor v1(0) xor v2(0) xor v3(0);
        else generate
            hash(0)((WORD_WIDTH*2)-1 downto WORD_WIDTH) <= v1(0) xor v3(0);
        end generate;

        -- generating register for xoring v1 with 0xdd
        -- ================================================
        --                     REGISTER
        -- ================================================
        hash_ext_reg_g: if REG_SETUP_EXT_START_REG = '1' generate
            process (CLK)
            begin
                if rising_edge(CLK) then
                    v0_hesr   <= v0(HASH_PIPE_LENGTH-1);
                    v1_hesr   <= v1(HASH_PIPE_LENGTH-1);
                    v2_hesr   <= v2(HASH_PIPE_LENGTH-1);
                    v3_hesr   <= v3(HASH_PIPE_LENGTH-1);
                    meta_hesr <= meta(HASH_PIPE_LENGTH-1);
                    vld_hesr  <= vld(HASH_PIPE_LENGTH-1);
                    hash_hesr <= hash(HASH_PIPE_LENGTH-1)(WORD_WIDTH-1 downto 0);

                    if (RESET = '1') then
                        vld_hesr <= '0';
                    end if;
                end if;
            end process;
        else generate
            v0_hesr   <= v0(HASH_PIPE_LENGTH-1);
            v1_hesr   <= v1(HASH_PIPE_LENGTH-1);
            v2_hesr   <= v2(HASH_PIPE_LENGTH-1);
            v3_hesr   <= v3(HASH_PIPE_LENGTH-1);
            meta_hesr <= meta(HASH_PIPE_LENGTH-1);
            vld_hesr  <= vld(HASH_PIPE_LENGTH-1);
            hash_hesr <= hash(HASH_PIPE_LENGTH-1)(WORD_WIDTH-1 downto 0);
        end generate;
    -- ================================================

    else generate
        -- generating hash differently for SipHash and HalfSipHash.
        hash_g: if WORD_WIDTH = 64 generate
            hash(0)(WORD_WIDTH-1 downto 0)              <= v0(0) xor v1(0) xor v2(0) xor v3(0);
            hash(0)((WORD_WIDTH*2)-1 downto WORD_WIDTH) <= (others => '0');
        else generate
            hash(0)(WORD_WIDTH-1 downto 0)              <= v1(0) xor v3(0);
            hash(0)((WORD_WIDTH*2)-1 downto WORD_WIDTH) <= (others => '0');
        end generate;
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    output_reg: if OUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_HASH  <= std_logic_vector(hash(0)(HASH_WIDTH-1 downto 0));
                OUT_META  <= meta(0);
                OUT_VALID <= vld(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_HASH  <= std_logic_vector(hash(0)(HASH_WIDTH-1 downto 0));
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;
end architecture;
