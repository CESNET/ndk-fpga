-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.hash_pack.all;

-- Compression function of the PCASD algorithm.
-- The function consists of a CA component which
-- takes the key block as an input and then
-- the output is fed into a mixing function.
--
-- There are two mixing function to choose from:
-- RD_ROUND and SIPROUND.
--
-- RD_ROUND is a mixing function from the definition
-- of PCASD and is similar to SHA-2 mixing function,
-- downscaled to 32 bits.
-- At minimum 8 rounds are required, but 32 and more
-- are recommended for the function to be effective
-- (definition of PCASD uses 64).
--
-- SIPROUND is an ARX (Addition, Rotation, Xor) used
-- by the siphash algorithm. In theory, it should offer
-- better diffusion with less rounds per block then
-- the SHA-2 style mix function, consuming less resources
-- in the process. At minimum 2 rounds should be used,
-- 8 and more are recommended.
entity PCASD_COMPRESS_BLOCK is
    generic (
        -- width of the block of the key to be compressed.
        BLOCK_WIDTH               : natural   := 256;
        -- width of the passthrough metadata
        META_WIDTH                : natural   := 32;
        -- number of rounds of the celluar automaton
        CA_ROUNDS                 : natural   := 4;
        -- number of rounds of the mix function
        MIX_ROUNDS                : natural   := 8;
        -- index of the block being compressed
        BLOCK_INDEX               : natural   := 0;
        -- level of the tree this block is in
        TREE_LEVEL                : natural   := 0;
        -- chosen chaotic rules of the celluar automaton
        CA_RULES                  : n_array_t := (90, 105, 60, 75, 135, 165, 149, 45, 89, 150, 30, 101, 102, 153, 86, 195);
        -- chosen mix function. "RD_ROUND" or "SIPROUND".
        MIX_FUNCTION              : string    := "RD_ROUND";
        -- register setup of the component
        REG_SETUP                 : std_logic_vector
    );
    port (
        -- main clock
        CLK         : in  std_logic;
        -- synchronious reset
        RESET       : in  std_logic;
        -- key block input
        IN_BLOCK    : in  unsigned(BLOCK_WIDTH-1 downto 0);
        -- seed is used to determine the celluar automaton rule
        IN_SEED     : in  unsigned(128-1 downto 0);
        -- metadata input
        IN_META     : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID    : in  std_logic;

        -- compression result output
        OUT_TEMP    : out unsigned(BLOCK_WIDTH-1 downto 0);
        -- seed passthrough
        OUT_SEED    : out unsigned(128-1 downto 0);
        -- metadata output
        OUT_META    : out std_logic_vector(META_WIDTH-1 downto 0);
        -- valid passthrough
        OUT_VALID   : out std_logic
    );
end entity;

architecture FULL of PCASD_COMPRESS_BLOCK is
    -- returns the length of the mix function pipeline
    function f_get_mix_function_high (mix_function: string; mix_rounds: natural; word64_count: natural) return natural is
        variable res : natural := 0;
    begin
        case mix_function is
            when "RD_ROUND" => res := mix_rounds + 1;
            when "SIPROUND" => res := word64_count + 1;
            when others => null;
        end case;

        return res;

    end function;

    -- width of the seed used to determine the CA rule.
    constant SEED_WIDTH           : natural := 128;
    -- number of 64-bit words, used by SIPROUND.
    constant WORD64_COUNT         : natural := BLOCK_WIDTH / 64;
    -- width of the slice of the extended key.
    constant EXT_KEY_SLICE_WIDTH  : natural := BLOCK_WIDTH + 32;
    -- length of the mix function pipeline.
    constant MIX_FUNCTION_HIGH    : natural := f_get_mix_function_high(MIX_FUNCTION, MIX_ROUNDS, WORD64_COUNT);
    constant MIX_ROUNDS_HIGH      : natural := REG_SETUP'high;
    -- sip compress word pipe length
    constant SCW_PIPE_LENGTH      : natural := MIX_ROUNDS * 4 + 2;
    -- length of the pipeline of this component.
    constant PIPE_LENGTH          : natural := CA_ROUNDS + MIX_FUNCTION_HIGH;

    -- logic
    -- result of the compression function
    signal result          : unsigned(BLOCK_WIDTH-1 downto 0);
    -- seed rotated based on index
    signal rotated_seed    : unsigned(128-1 downto 0);

    -- registers
    -- rule used by the celluar automaton
    signal ca_rule         : u_array_t(PIPE_LENGTH-1 downto MIX_FUNCTION_HIGH-1)(8-1 downto 0);
    -- intermediate result of the random diffusion component
    signal temp            : u_array_t(MIX_ROUNDS downto 0)(EXT_KEY_SLICE_WIDTH-1 downto 0);
    -- variables used by the mix functions
    signal h0              : u_array_t(MIX_FUNCTION_HIGH-1 downto 0)(64-1 downto 0);
    signal h1              : u_array_t(MIX_FUNCTION_HIGH-1 downto 0)(64-1 downto 0);
    signal h2              : u_array_t(MIX_FUNCTION_HIGH-1 downto 0)(64-1 downto 0);
    signal h3              : u_array_t(MIX_FUNCTION_HIGH-1 downto 0)(64-1 downto 0);
    -- key input and intermediate result of celluar automaton rounds
    signal key_block_reg   : u_array_t(PIPE_LENGTH-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    -- seed used to determine the rule of the celluar automaton
    signal seed            : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    -- validity signal
    signal vld             : std_logic_vector(PIPE_LENGTH-1 downto 0);
    -- meta values
    signal meta            : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    -- joined meta and seed signal used to pass both signals through the SIP_COMPRESS_WORD component
    signal seed_and_meta   : slv_array_t(MIX_FUNCTION_HIGH-1 downto 0)(SEED_WIDTH + META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key_block_reg(PIPE_LENGTH-1) <= IN_BLOCK;
    seed(PIPE_LENGTH-1)          <= IN_SEED;
    vld(PIPE_LENGTH-1)           <= IN_VALID;
    meta(PIPE_LENGTH-1)          <= IN_META;

    -- using the 4 bits on the index of this block to determine the rule used in the celular automaton.
    rotated_seed           <= rotate_right(IN_SEED, BLOCK_INDEX * 4);
    ca_rule(PIPE_LENGTH-1) <= to_unsigned(CA_RULES(to_integer(rotated_seed(4-1 downto 0))), 8);

    -- ================================================
    --                     LOGIC
    -- ================================================
    -- generating the rounds of celluar automaton
    ca_g: for g in PIPE_LENGTH-1 downto MIX_FUNCTION_HIGH generate
        ca_round_i: entity work.PCASD_CA_ROUND
        generic map (
            STATE_WIDTH => BLOCK_WIDTH,
            META_WIDTH  => META_WIDTH,
            OUT_REG     => REG_SETUP(g - MIX_FUNCTION_HIGH + 1) = '1'
        ) port map (
            CLK         => CLK,
            RESET       => RESET,
            IN_STATE    => key_block_reg(g),
            IN_RULE     => ca_rule(g),
            IN_SEED     => seed(g),
            IN_META     => meta(g),
            IN_VALID    => vld(g),
            OUT_STATE   => key_block_reg(g-1),
            OUT_RULE    => ca_rule(g-1),
            OUT_SEED    => seed(g-1),
            OUT_META    => meta(g-1),
            OUT_VALID   => vld(g-1)
        );
    end generate;

    -- generating the random diffusion component of PCASD
    mix_function_g: if MIX_FUNCTION = "RD_ROUND" generate
        -- checking number of mix rounds
        assert MIX_ROUNDS < 64
            report "Maximum number of mix rounds is 64."
            severity error;

        -- setting the initial values of the registers
        h0(MIX_ROUNDS)(32-1 downto 0)  <= X"C4CA4238";
        h0(MIX_ROUNDS)(64-1 downto 32) <= X"C81E728D";
        h1(MIX_ROUNDS)(32-1 downto 0)  <= X"ECCBC87E";
        h1(MIX_ROUNDS)(64-1 downto 32) <= X"A87FF679";
        h2(MIX_ROUNDS)(32-1 downto 0)  <= X"E4DA3B7F";
        h2(MIX_ROUNDS)(64-1 downto 32) <= X"1679091C";
        h3(MIX_ROUNDS)(32-1 downto 0)  <= X"8F14E45F";
        h3(MIX_ROUNDS)(64-1 downto 32) <= X"C9F0F895";

        -- using the result of the CA rounds as initial value of the key
        temp(MIX_ROUNDS) <= resize(key_block_reg(MIX_ROUNDS), EXT_KEY_SLICE_WIDTH);

        -- generating the random diffusion rounds
        rd_g: for g in MIX_ROUNDS downto 1 generate
            rd_round_i: entity work.PCASD_RD_ROUND
            generic map (
                KEY_WIDTH   => EXT_KEY_SLICE_WIDTH,
                BLOCK_WIDTH => BLOCK_WIDTH,
                META_WIDTH  => META_WIDTH,
                RD_ROUNDS   => MIX_ROUNDS,
                ROUND_INDEX => MIX_ROUNDS - g,
                CA_RULES    => CA_RULES,
                REG_SETUP   => REG_SETUP(MIX_ROUNDS_HIGH - (MIX_ROUNDS - g) * 6 downto MIX_ROUNDS_HIGH - (MIX_ROUNDS - g + 1) * 6 + 1)
            ) port map (
                CLK        => CLK,
                RESET      => RESET,
                IN_KEY     => temp(g),
                IN_A       => h0(g)(32-1 downto 0),
                IN_B       => h0(g)(64-1 downto 32),
                IN_C       => h1(g)(32-1 downto 0),
                IN_D       => h1(g)(64-1 downto 32),
                IN_E       => h2(g)(32-1 downto 0),
                IN_F       => h2(g)(64-1 downto 32),
                IN_G       => h3(g)(32-1 downto 0),
                IN_H       => h3(g)(64-1 downto 32),
                IN_SEED    => seed(g),
                IN_META    => meta(g),
                IN_VALID   => vld(g),
                OUT_KEY    => temp(g-1),
                OUT_A      => h0(g-1)(32-1 downto 0),
                OUT_B      => h0(g-1)(64-1 downto 32),
                OUT_C      => h1(g-1)(32-1 downto 0),
                OUT_D      => h1(g-1)(64-1 downto 32),
                OUT_E      => h2(g-1)(32-1 downto 0),
                OUT_F      => h2(g-1)(64-1 downto 32),
                OUT_G      => h3(g-1)(32-1 downto 0),
                OUT_H      => h3(g-1)(64-1 downto 32),
                OUT_SEED   => seed(g-1),
                OUT_META   => meta(g-1),
                OUT_VALID  => vld(g-1)
            );
        end generate;

    -- generating the compress function of SipHash (PCARX)
    elsif MIX_FUNCTION = "SIPROUND" generate
        -- setting the initial values of the registers
        h0(WORD64_COUNT) <= X"736F6D6570736575";
        h1(WORD64_COUNT) <= X"646F72616E646F6D";
        h2(WORD64_COUNT) <= X"6C7967656E657261";
        h3(WORD64_COUNT) <= X"7465646279746573";

        -- concanating the seed and meta signals
        seed_and_meta(WORD64_COUNT) <= std_logic_vector(seed(WORD64_COUNT)) & meta(WORD64_COUNT);

        -- generating compression function for each word
        sip_compress_word_g: for g in WORD64_COUNT downto 1 generate

            sip_compress_word_i: entity work.SIP_COMPRESS_WORD
            generic map (
                KEY_OFFSET         => WORD64_COUNT - g,
                KEY_WIDTH          => BLOCK_WIDTH,
                META_WIDTH         => SEED_WIDTH + META_WIDTH,
                ROUNDS             => MIX_ROUNDS,
                WORD_WIDTH         => 64,
                FINAL_WORD         => WORD64_COUNT - g = WORD64_COUNT,
                FINAL_CONST        => 255,
                REG_SETUP          => REG_SETUP(MIX_ROUNDS_HIGH - (WORD64_COUNT - g) * SCW_PIPE_LENGTH downto MIX_ROUNDS_HIGH - (WORD64_COUNT - g + 1) * SCW_PIPE_LENGTH + 1)
            ) port map (
                CLK                => CLK,
                RESET              => RESET,
                IN_KEY             => key_block_reg(g),
                IN_V0              => h0(g),
                IN_V1              => h1(g),
                IN_V2              => h2(g),
                IN_V3              => h3(g),
                IN_META            => seed_and_meta(g),
                IN_VALID           => vld(g),
                OUT_KEY            => key_block_reg(g-1),
                OUT_V0             => h0(g-1),
                OUT_V1             => h1(g-1),
                OUT_V2             => h2(g-1),
                OUT_V3             => h3(g-1),
                OUT_META           => seed_and_meta(g-1),
                OUT_VALID          => vld(g-1)
            );
        end generate;

        -- spliting seed and meta signals
        meta(0) <= seed_and_meta(0)(META_WIDTH-1 downto 0);
        seed(0) <= unsigned(seed_and_meta(0)(SEED_WIDTH + META_WIDTH-1 downto META_WIDTH));

    else generate
        assert false
            report "Unknown mix function '" & MIX_FUNCTION & "'."
            severity error;
    end generate;

    -- concanating the registers to generate compression function result
    result <= h3(0) & h2(0) & h1(0) & h0(0);

    -- ================================================
    --                     OUTPUT
    -- ================================================
    OUT_TEMP  <= result(BLOCK_WIDTH-1 downto 0);
    OUT_SEED  <= seed(0);
    OUT_META  <= meta(0);
    OUT_VALID <= vld(0);

end architecture;
