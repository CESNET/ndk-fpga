-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Firmware implementation of key block processing component of the CHASKEY hash function.
--
-- Combines 128-bit block of the key with state variables using the xor operation
-- and mixes the state variables with [ROUNDS] rounds of permutations.
--
-- This entity includes the CHASKEY_ROUND component. The components are connected in
-- the following manner:
--
--                           INPUT                              PERMUTATIONS
--                                                       +------------------------+
-- IN ---[v(3:0)(31:0) xor key((off+1)*128 : off*128)]---| CHASKEY_ROUND * ROUNDS |--- OUT
--                                                       +------------------------+
--
entity CHASKEY_PROCESS_BLOCK is
    generic (
        -- which 128-bit word of the key shall be processed.
        KEY_OFFSET      : natural := 0;
        -- width of the whole key.
        KEY_WIDTH       : natural := 312;
        -- width of the passthrough metadata.
        META_WIDTH      : natural := 32;
        -- number of sipround rounds generate.
        ROUNDS          : natural := 8;
        -- setup of the registers of this components.
        REG_SETUP       : std_logic_vector
    );
    port (
        -- main clock
        CLK             : in  std_logic;
        -- synchronious reset
        RESET           : in  std_logic;
        -- key passthrough input
        IN_KEY          : in  unsigned(KEY_WIDTH-1 downto 0);
        -- seed passthrough input
        IN_SEED         : in  unsigned(128-1 downto 0);
        -- internal state variables input
        IN_V0           : in  unsigned(32-1 downto 0);
        IN_V1           : in  unsigned(32-1 downto 0);
        IN_V2           : in  unsigned(32-1 downto 0);
        IN_V3           : in  unsigned(32-1 downto 0);
        -- metadata input
        IN_META         : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID        : in  std_logic;

        -- key passthrough output
        OUT_KEY         : out unsigned(KEY_WIDTH-1 downto 0);
        -- seed passthrough output
        OUT_SEED        : out unsigned(128-1 downto 0);
        -- internal state variables output
        OUT_V0          : out unsigned(32-1 downto 0);
        OUT_V1          : out unsigned(32-1 downto 0);
        OUT_V2          : out unsigned(32-1 downto 0);
        OUT_V3          : out unsigned(32-1 downto 0);
        -- metadata output
        OUT_META        : out std_logic_vector(META_WIDTH-1 downto 0);
        -- valid passthrough
        OUT_VALID       : out std_logic
    );
end entity;

architecture FULL of CHASKEY_PROCESS_BLOCK is
    -- length of the pipeline of this component
    constant PIPE_LENGTH   : natural := ROUNDS + 2;
    constant SCALED_OFFSET : natural := KEY_OFFSET * 128;

    -- registers
    signal v0   : u_array_t(PIPE_LENGTH-1 downto 0)(32-1 downto 0);
    signal v1   : u_array_t(PIPE_LENGTH-1 downto 0)(32-1 downto 0);
    signal v2   : u_array_t(PIPE_LENGTH-1 downto 0)(32-1 downto 0);
    signal v3   : u_array_t(PIPE_LENGTH-1 downto 0)(32-1 downto 0);
    signal key  : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal seed : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    signal vld  : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key(PIPE_LENGTH-1)  <= IN_KEY;
    seed(PIPE_LENGTH-1) <= IN_SEED;
    vld(PIPE_LENGTH-1)  <= IN_VALID;
    meta(PIPE_LENGTH-1) <= IN_META;

    -- combining the block of the key that's being processed with the state variables
    -- using xor.
    v0(PIPE_LENGTH-1)   <= IN_V0 xor IN_KEY(SCALED_OFFSET +  32-1 downto SCALED_OFFSET +  0);
    v1(PIPE_LENGTH-1)   <= IN_V1 xor IN_KEY(SCALED_OFFSET +  64-1 downto SCALED_OFFSET + 32);
    v2(PIPE_LENGTH-1)   <= IN_V2 xor IN_KEY(SCALED_OFFSET +  96-1 downto SCALED_OFFSET + 64);
    v3(PIPE_LENGTH-1)   <= IN_V3 xor IN_KEY(SCALED_OFFSET + 128-1 downto SCALED_OFFSET + 96);

    -- ================================================
    --                     LOGIC
    -- ================================================

    -- permutations of the state variables, number
    -- of permutations is decided by the ROUNDS generic.
    round_g: for g in PIPE_LENGTH-2 downto 1 generate
        process_block_round_i: entity work.CHASKEY_ROUND
        generic map (
            KEY_WIDTH  => KEY_WIDTH,
            META_WIDTH => META_WIDTH,
            REG_SETUP  => REG_SETUP(g * 4 - 1 downto (g - 1) * 4)
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => key(g),
            IN_SEED    => seed(g),
            IN_V0      => v0(g),
            IN_V1      => v1(g),
            IN_V2      => v2(g),
            IN_V3      => v3(g),
            IN_META    => meta(g),
            IN_VALID   => vld(g),
            OUT_KEY    => key(g-1),
            OUT_SEED   => seed(g-1),
            OUT_V0     => v0(g-1),
            OUT_V1     => v1(g-1),
            OUT_V2     => v2(g-1),
            OUT_V3     => v3(g-1),
            OUT_META   => meta(g-1),
            OUT_VALID  => vld(g-1)
        );
    end generate;

    -- ================================================
    --                    PIPELINE
    -- ================================================

    -- generating the a register between INPUT and PERMUTATIONS
    -- if START REG is set to true.
    end_reg_g: if REG_SETUP(REG_SETUP'high) generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                key(PIPE_LENGTH-2)  <= key(PIPE_LENGTH-1);
                seed(PIPE_LENGTH-2) <= seed(PIPE_LENGTH-1);
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
        seed(PIPE_LENGTH-2) <= seed(PIPE_LENGTH-1);
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
    -- no need for a register here, because the result
    -- of ROUND is simply passed on with no modification.
    OUT_KEY   <= key(0);
    OUT_SEED  <= seed(0);
    OUT_V0    <= v0(0);
    OUT_V1    <= v1(0);
    OUT_V2    <= v2(0);
    OUT_V3    <= v3(0);
    OUT_META  <= meta(0);
    OUT_VALID <= vld(0);

end architecture;
