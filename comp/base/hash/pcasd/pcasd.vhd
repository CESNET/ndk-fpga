-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;
use work.hash_pack.all;

-- Firmware implementation of a scaled down version of the PCASD hash
-- function using variable pipeline intended for use in high speed
-- networking applications.
--
-- PCASD is a cryptographic hash function based on parallel structures,
-- celluar automata and stochastic diffusion.
--
-- The bases of PCASD is it's compression function h, which consists
-- of celluar automata component, the result of which is then fed into
-- a random diffusion component, consisting of key extension and
-- mixing function simillar to SHA-2.
--
-- After the number of key blocks is established, a parallel structure
-- like this is generated:
--
--      key[0]--(h)--+
--                  (+)--(h)--+
--      key[1]--(h)--+        |
--                           (+)-- ...
--      key[2]--(h)--+        |
--                  (+)--(h)--+
--      key[3]--(h)--+
--                                  ... --(h)--+
--      ...                                   (+)-- hash
--                                  ... --(h)--+
--      key[n]---(h)-----(h)--- ...
--
-- Given the hardware constraints, this implementation is a minimised version
-- of PCASD and differs from it in a few key areas - the block width is 256 bits
-- opposed to 512-bits, registers in the mix function of the random diffusion
-- components are 32-bit opposed to 64-bit and generally less mixing rounds
-- can be generated in order to keep the ALM consumption reasonable.
--
-- The number of rounds of the celluar automaton per compression function
-- can be set by using the CA_ROUNDS generic, number of mix function rounds
-- by the MIX_ROUNDS generic. When it comes to CA rounds, since celluar
-- automatons are cheaper in terms of resources then mixing functions,
-- the more is better to compensate for the lower number of mixing rounds.
-- It is recommended to use four or more. Number of recommended mixing rounds
-- differ based on the compression function that is used.
--
-- The random diffusion function as defined by PCASD can be generated
-- by setting the MIX_FUNCTION generic to "RD_ROUND".
-- At minimum 8 rounds should be used, 16 rounds and more is recommended.
--
-- In order to lower ALM consumption further, ARX mix function from the
-- siphash algorithm can be used by setting the MIX_FUNCTION generic
-- to "SIPROUND" (PCARX). At least 2 rounds should be used, 8 is recommended.
entity PCASD is
    generic (
        -- width of the input key.
        -- If not aligned to whole bytes, the rest is extended by zeros.
        KEY_WIDTH               : natural   := 312;
        -- width of the generated hash, max 128 bits.
        HASH_WIDTH              : natural   := 128;
        -- width of the passthrough metadata.
        META_WIDTH              : natural   := 32;
        -- width of a block of a key.
        BLOCK_WIDTH             : natural   := 256;
        -- number of rounds of celluar automaton per message block.
        CA_ROUNDS               : natural   := 4;
        -- number of mix functions per message block.
        MIX_ROUNDS              : natural   := 16;
        -- type of the mix function. "RD_ROUND" for SHA-2-style mix function,
        -- "SIPROUND" for ARX-style mix function.
        MIX_FUNCTION            : string    := "RD_ROUND";
        -- adds a register to the output.
        OUT_REG                 : boolean   := true;

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
        -- register setup of a CA round component
        CA_ROUND_REG_SETUP        : std_logic_vector(1-1 downto 0)  := "1";
        -- register setup of the mix function component
        MIX_FUNCTION_REG_SETUP    : std_logic_vector(6-1 downto 0)  := "111111";
        -- ads register after adding results of compression function nodes
        NODE_ADD_REG_SETUP        : std_logic_vector(1-1 downto 0)  := "1"

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

architecture FULL of PCASD is
    -- returns minimum number of bits to represent the
    -- value of passed natural.
    function f_bit_length (val: natural) return natural is
        variable v   : natural := val;
        variable len : natural := 0;
    begin
        if (val = 0) then
            return 1;
        end if;

        while v > 0 loop
            len := len + 1;
            v   := v / 2;
        end loop;

        return len;
    end function;

    -- returns array of naturals with number of compression functions per level
    -- of the tree of the parallel structure.
    function f_get_compressions_per_tree_level (block_count: natural) return n_array_t is
        variable v   : natural := block_count;
        variable res : n_array_t(f_bit_length(block_count - 1)-1 downto 0);
    begin
        for i in res'high downto res'low loop
            res(i) := v;
            v      := div_roundup(v, 2);
        end loop;

        return res;
    end function;

    -- returns array of naturals with start index of the compression
    -- function per tree level. Taktes compressions per tree level
    -- as argument.
    function f_get_level_start_index (cptl: n_array_t) return n_array_t is
        variable v   : natural := 0;
        variable res : n_array_t(cptl'high downto cptl'low);
    begin
        for i in res'high downto res'low loop
            res(i) := v;
            v      := v + cptl(i);
        end loop;

        return res;
    end function;

    function f_get_mix_reg_setup (reg_setup: std_logic_vector; mix_rounds: natural; mix_function: string) return std_logic_vector is
    begin
        case mix_function is
            when "RD_ROUND" =>
                return f_duplicate_std_logic_vector(reg_setup, mix_rounds);
            when "SIPROUND" =>
                return f_duplicate_std_logic_vector(reg_setup(5) & f_duplicate_std_logic_vector(reg_setup(4 downto 1), mix_rounds) & reg_setup(0), 4);
            when others =>
                return "0";
        end case;
    end function;

    -- width of the key aligned to whole bytes
    constant KEY_WIDTH_BYTE_ALIGNED  : natural := div_roundup(KEY_WIDTH, 8) * 8;
    -- width of the number representing the length of the original message placed
    -- at the end of the padded message
    constant KEY_LENGTH_PAD_WIDTH    : natural := BLOCK_WIDTH / 8;
    -- width of the key aligned to whole words and extended by a extra word
    constant KEY_WIDTH_BLOCK_ALIGNED : natural := div_roundup(KEY_WIDTH + KEY_LENGTH_PAD_WIDTH + 8, BLOCK_WIDTH) * BLOCK_WIDTH;
    -- number of components processing key blocks to be generated
    constant BLOCK_COUNT             : natural := KEY_WIDTH_BLOCK_ALIGNED / BLOCK_WIDTH;
    -- number of levels of the tree parallel structure
    constant TREE_LEVELS             : natural := f_bit_length(BLOCK_COUNT - 1);
    -- compression functions generated per tree level
    constant CPTL                    : n_array_t(TREE_LEVELS-1 downto 0) := f_get_compressions_per_tree_level(BLOCK_COUNT);
    -- start indexes of first compression functions of the levels of the tree
    constant LEVEL_START_INDEX       : n_array_t(TREE_LEVELS-1 downto 0) := f_get_level_start_index(CPTL);
    -- set of chaotic rules used in compression function
    constant CA_RULES                : n_array_t := (90, 105, 60, 75, 135, 165, 149, 45, 89, 150, 30, 101, 102, 153, 86, 195);
    -- length of the pipeline of this component
    constant PIPE_LENGTH             : natural := TREE_LEVELS * 2;
    -- manual setting of the registers of PCASD_COMPRESS_BLOCK components
    constant TREE_LEVEL_REG_SETUP    : std_logic_vector := f_duplicate_std_logic_vector(CA_ROUND_REG_SETUP, CA_ROUNDS) & f_get_mix_reg_setup(MIX_FUNCTION_REG_SETUP, MIX_ROUNDS, MIX_FUNCTION) & NODE_ADD_REG_SETUP;
    -- length of the pipeline of the compression function
    constant COMPRESSION_PIPE_LENGTH : natural := TREE_LEVEL_REG_SETUP'length;
    -- actual setup of the pipeline of tree levels (components of the tree level share this configuration)
    constant REG_SETUP_TREE_LEVELS   : slv_array_t(TREE_LEVELS-1 downto 0)(COMPRESSION_PIPE_LENGTH - 1 downto 0) := f_get_reg_setup(TREE_LEVELS, COMPRESSION_PIPE_LENGTH, 0, REG_SETUP, REG_SETUP_MANUAL_OVERRIDE, TREE_LEVEL_REG_SETUP);

    -- logic
    -- signal used as input and output of the compression blocks of the parallel
    -- tree structure
    signal temp     : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH_BLOCK_ALIGNED-1 downto 0);

    -- registers
    signal key      : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH_BLOCK_ALIGNED-1 downto 0);
    signal seed     : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    signal meta     : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    signal vld      : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal hash     : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal temp_reg : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH_BLOCK_ALIGNED-1 downto 0);

begin
    assert HASH_WIDTH <= 128
        report "HASH_WIDTH must not be greater than 128 bits."
        severity error;

    -- ================================================
    --                     INPUT
    -- ================================================
    -- key padding
    temp_reg(PIPE_LENGTH-1)(KEY_WIDTH_BYTE_ALIGNED-1 downto 0)                                              <= resize(unsigned(IN_KEY), KEY_WIDTH_BYTE_ALIGNED);
    temp_reg(PIPE_LENGTH-1)(KEY_WIDTH_BYTE_ALIGNED+8-1 downto KEY_WIDTH_BYTE_ALIGNED)                       <= X"80";
    temp_reg(PIPE_LENGTH-1)(KEY_WIDTH_BLOCK_ALIGNED-KEY_LENGTH_PAD_WIDTH-1 downto KEY_WIDTH_BYTE_ALIGNED+8) <= (others => '0');
    temp_reg(PIPE_LENGTH-1)(KEY_WIDTH_BLOCK_ALIGNED-1 downto KEY_WIDTH_BLOCK_ALIGNED-KEY_LENGTH_PAD_WIDTH)  <= to_unsigned(KEY_WIDTH, KEY_LENGTH_PAD_WIDTH);

    seed(PIPE_LENGTH-1) <= unsigned(IN_SEED);
    meta(PIPE_LENGTH-1) <= IN_META;
    vld(PIPE_LENGTH-1)  <= IN_VALID;

    -- ================================================
    --                     LOGIC
    -- ================================================
    -- generating tree levels
    tree_levels_g: for l in TREE_LEVELS - 1 downto 0 generate

        -- generating pairs and adding them together
        node_pairs_g: for g in (CPTL(l) / 2) - 1 downto 0 generate

            -- if this is the first node, it is used to pass seed, meta and valid through the level
            first_node_g: if g = 0 generate

                compress_block_top_i: entity work.PCASD_COMPRESS_BLOCK
                generic map (
                    BLOCK_WIDTH               => BLOCK_WIDTH,
                    META_WIDTH                => META_WIDTH,
                    CA_ROUNDS                 => CA_ROUNDS,
                    MIX_ROUNDS                => MIX_ROUNDS,
                    BLOCK_INDEX               => LEVEL_START_INDEX(l),
                    TREE_LEVEL                => TREE_LEVELS - l - 1,
                    CA_RULES                  => CA_RULES,
                    MIX_FUNCTION              => MIX_FUNCTION,
                    REG_SETUP                 => REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(COMPRESSION_PIPE_LENGTH-1 downto 1)
                ) port map (
                    CLK                       => CLK,
                    RESET                     => RESET,
                    IN_BLOCK                  => temp_reg(l * 2 + 1)((g * 2 + 1) * BLOCK_WIDTH - 1 downto g * 2 * BLOCK_WIDTH),
                    IN_SEED                   => seed(l * 2 + 1),
                    IN_META                   => meta(l * 2 + 1),
                    IN_VALID                  => vld(l * 2 + 1),
                    OUT_TEMP                  => temp_reg(l * 2)((g * 2 + 1) * BLOCK_WIDTH - 1 downto g * 2 * BLOCK_WIDTH),
                    OUT_SEED                  => seed(l * 2),
                    OUT_META                  => meta(l * 2),
                    OUT_VALID                 => vld(l * 2)
                );

            else generate

                compress_block_top_i: entity work.PCASD_COMPRESS_BLOCK
                generic map (
                    BLOCK_WIDTH               => BLOCK_WIDTH,
                    META_WIDTH                => META_WIDTH,
                    CA_ROUNDS                 => CA_ROUNDS,
                    MIX_ROUNDS                => MIX_ROUNDS,
                    BLOCK_INDEX               => LEVEL_START_INDEX(l) + g * 2,
                    TREE_LEVEL                => TREE_LEVELS - l - 1,
                    CA_RULES                  => CA_RULES,
                    MIX_FUNCTION              => MIX_FUNCTION,
                    REG_SETUP                 => REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(COMPRESSION_PIPE_LENGTH-1 downto 1)
                ) port map (
                    CLK                       => CLK,
                    RESET                     => RESET,
                    IN_BLOCK                  => temp_reg(l * 2 + 1)((g * 2 + 1) * BLOCK_WIDTH - 1 downto g * 2 * BLOCK_WIDTH),
                    IN_SEED                   => seed(l * 2 + 1),
                    IN_META                   => meta(l * 2 + 1),
                    IN_VALID                  => vld(l * 2 + 1),
                    OUT_TEMP                  => temp_reg(l * 2)((g * 2 + 1) * BLOCK_WIDTH - 1 downto g * 2 * BLOCK_WIDTH),
                    OUT_SEED                  => open,
                    OUT_META                  => open,
                    OUT_VALID                 => open
                );

            end generate;

            compress_block_bottom_i: entity work.PCASD_COMPRESS_BLOCK
            generic map (
                BLOCK_WIDTH               => BLOCK_WIDTH,
                META_WIDTH                => META_WIDTH,
                CA_ROUNDS                 => CA_ROUNDS,
                MIX_ROUNDS                => MIX_ROUNDS,
                BLOCK_INDEX               => LEVEL_START_INDEX(l) + g * 2 + 1,
                TREE_LEVEL                => TREE_LEVELS - l - 1,
                CA_RULES                  => CA_RULES,
                MIX_FUNCTION              => MIX_FUNCTION,
                REG_SETUP                 => REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(COMPRESSION_PIPE_LENGTH-1 downto 1)
            ) port map (
                CLK                       => CLK,
                RESET                     => RESET,
                IN_BLOCK                  => temp_reg(l * 2 + 1)((g * 2 + 2) * BLOCK_WIDTH - 1 downto (g * 2 + 1) * BLOCK_WIDTH),
                IN_SEED                   => seed(l * 2 + 1),
                IN_META                   => meta(l * 2 + 1),
                IN_VALID                  => vld(l * 2 + 1),
                OUT_TEMP                  => temp_reg(l * 2)((g * 2 + 2) * BLOCK_WIDTH - 1 downto (g * 2 + 1) * BLOCK_WIDTH),
                OUT_SEED                  => open,
                OUT_META                  => open,
                OUT_VALID                 => open
            );

            temp(l * 2)((g + 1) * BLOCK_WIDTH - 1 downto g * BLOCK_WIDTH) <= temp_reg(l * 2)((g * 2 + 1) * BLOCK_WIDTH - 1 downto g * 2 * BLOCK_WIDTH) + temp_reg(l * 2)((g * 2 + 2) * BLOCK_WIDTH - 1 downto (g * 2 + 1) * BLOCK_WIDTH);

        end generate;

        -- generating node that doesn't have a pair
        single_node_g: if CPTL(l) mod 2 = 1 generate

            -- if this is the only node, it is used to pass seed, meta and valid through the level
            only_node_g: if CPTL(l) = 1 generate

                compress_block_single_i: entity work.PCASD_COMPRESS_BLOCK
                generic map (
                    BLOCK_WIDTH               => BLOCK_WIDTH,
                    META_WIDTH                => META_WIDTH,
                    CA_ROUNDS                 => CA_ROUNDS,
                    MIX_ROUNDS                => MIX_ROUNDS,
                    BLOCK_INDEX               => LEVEL_START_INDEX(l) + CPTL(l) - 1,
                    TREE_LEVEL                => TREE_LEVELS - l - 1,
                    CA_RULES                  => CA_RULES,
                    MIX_FUNCTION              => MIX_FUNCTION,
                    REG_SETUP                 => REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(COMPRESSION_PIPE_LENGTH-1 downto 1)
                ) port map (
                    CLK                       => CLK,
                    RESET                     => RESET,
                    IN_BLOCK                  => temp_reg(1),
                    IN_SEED                   => seed(1),
                    IN_META                   => meta(1),
                    IN_VALID                  => vld(1),
                    OUT_TEMP                  => temp(0),
                    OUT_SEED                  => seed(0),
                    OUT_META                  => meta(0),
                    OUT_VALID                 => vld(0)
                );

            else generate

                compress_block_single_i: entity work.PCASD_COMPRESS_BLOCK
                generic map (
                    BLOCK_WIDTH               => BLOCK_WIDTH,
                    META_WIDTH                => META_WIDTH,
                    CA_ROUNDS                 => CA_ROUNDS,
                    MIX_ROUNDS                => MIX_ROUNDS,
                    BLOCK_INDEX               => LEVEL_START_INDEX(l) + CPTL(l) - 1,
                    TREE_LEVEL                => TREE_LEVELS - l - 1,
                    CA_RULES                  => CA_RULES,
                    MIX_FUNCTION              => MIX_FUNCTION,
                    REG_SETUP                 => REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(COMPRESSION_PIPE_LENGTH-1 downto 1)
                ) port map (
                    CLK                       => CLK,
                    RESET                     => RESET,
                    IN_BLOCK                  => temp_reg(l * 2 + 1)(CPTL(l) * BLOCK_WIDTH - 1 downto (CPTL(l) - 1) * BLOCK_WIDTH),
                    IN_SEED                   => seed(l * 2 + 1),
                    IN_META                   => meta(l * 2 + 1),
                    IN_VALID                  => vld(l * 2 + 1),
                    OUT_TEMP                  => temp_reg(l * 2)(CPTL(l) * BLOCK_WIDTH - 1 downto (CPTL(l) - 1) * BLOCK_WIDTH),
                    OUT_SEED                  => open,
                    OUT_META                  => open,
                    OUT_VALID                 => open
                );

                -- set the last result of the next level
                temp(l * 2)(CPTL(l - 1) * BLOCK_WIDTH - 1 downto (CPTL(l - 1) - 1) * BLOCK_WIDTH) <= temp_reg(l * 2)(CPTL(l) * BLOCK_WIDTH - 1 downto (CPTL(l) - 1) * BLOCK_WIDTH);

            end generate;

        end generate;

    end generate;

    hash <= std_logic_vector(temp(0)(HASH_WIDTH-1 downto 0));

    -- ================================================
    --                     PIPELINE
    -- ================================================
    tree_pipeline_g: for l in TREE_LEVELS - 1 downto 1 generate

        reg_g: if REG_SETUP_TREE_LEVELS(TREE_LEVELS - l - 1)(0) = '1' generate

            process (CLK)
            begin
                if rising_edge(CLK) then
                    temp_reg(l * 2 - 1) <= temp(l * 2);
                    seed(l * 2 - 1)     <= seed(l * 2);
                    meta(l * 2 - 1)     <= meta(l * 2);
                    vld(l * 2 - 1)      <= vld(l * 2);

                    if (RESET = '1') then
                        vld(l * 2 - 1)  <= '0';
                    end if;
                end if;
            end process;

        else generate
            temp_reg(l * 2 - 1) <= temp(l * 2);
            seed(l * 2 - 1)     <= seed(l * 2);
            meta(l * 2 - 1)     <= meta(l * 2);
            vld(l * 2 - 1)      <= vld(l * 2);

        end generate;

    end generate;


    -- ================================================
    --                     OUTPUT
    -- ================================================
    output_reg: if OUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_HASH  <= hash;
                OUT_META  <= meta(0);
                OUT_VALID <= vld(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_HASH  <= hash;
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;

end architecture;
