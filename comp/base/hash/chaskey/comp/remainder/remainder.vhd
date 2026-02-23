-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2026 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Firmware implementation of remainder processing component of the CHASKEY hash function.
--
-- Combines last 128-bit block or remainder alligned to 128-bit with padding of the key
-- and shifted seed with state variables and mixes them with last [ROUNDS] rounds of permutations.
--
-- The CHASKEY_REMAINDER entity includes the CHASKEY_ROUND component. The individual parts are
-- connected as following:
--
--
--
-- IN -+-------[v(3:0)(31:0) xor key(127:0)]-------+--{[(seed << 1) xor (seed(127)? 0x87:0x00)}--[v(3:0)(31:0) xor seed(127:0)]-->
--     |                                           |             if key is not aligned
--     +-[(seed << 1) xor (seed(127))? 0x87:0x00)]-+
--
--
--     +------------------------+
-- >---| CHASKEY_ROUND * ROUNDS |---[v(3:0)(31:0) xor seed(127:0)]--- OUT
--     +------------------------+
--
entity CHASKEY_REMAINDER is
    generic (
        -- width of the passthrough metadata
        META_WIDTH      : natural := 32;
        -- number of sipround rounds generate
        ROUNDS          : natural := 8;
        -- number of remaining bytes
        REMAIN          : natural := 0;
        -- setup of the registers of CHASKEY_ROUND components
        ROUND_REG_SETUP : std_logic_vector(4-1 downto 0) := "1111";
        -- setup of the registers of this components
        REG_SETUP       : std_logic_vector(4-1 downto 0) := "1111"
    );
    port (
        -- main clock
        CLK             : in  std_logic;
        -- synchronious reset
        RESET           : in  std_logic;
        -- remainder of the key
        IN_KEY          : in  unsigned(128-1 downto 0);
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

architecture FULL of CHASKEY_REMAINDER is
    -- returns the length of the pipe for components surrounding the round functions
    function f_get_pipe_length (remain: natural) return natural is
    begin
        if (remain = 0) then
            return 3;
        else
            return 4;
        end if;
    end function;

    -- length of the pipeline of this component
    constant PIPE_LENGTH : natural := ROUNDS + f_get_pipe_length(REMAIN);

    -- logic
    signal seed     : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    signal v0       : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v1       : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v2       : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v3       : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);

    -- registers
    signal vld      : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta     : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);
    signal seed_reg : u_array_t(PIPE_LENGTH-1 downto 0)(128-1 downto 0);
    signal v0_reg   : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v1_reg   : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v2_reg   : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);
    signal v3_reg   : u_array_t(PIPE_LENGTH-1 downto 0)( 32-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================

    -- bit-shifting the seed and applying the 0x87 constant
    -- in case of overflow.
    process (all)
    begin
        if (IN_SEED(127) = '1') then
            seed(PIPE_LENGTH-1) <= shift_left(IN_SEED, 1) xor to_unsigned(135, 128);
        else
            seed(PIPE_LENGTH-1) <= shift_left(IN_SEED, 1);
        end if;
    end process;

    vld(PIPE_LENGTH-1)  <= IN_VALID;
    meta(PIPE_LENGTH-1) <= IN_META;

    -- combining the state variables with the remainder of the key.
    v0(PIPE_LENGTH-1)   <= IN_V0 xor IN_KEY( 32-1 downto  0);
    v1(PIPE_LENGTH-1)   <= IN_V1 xor IN_KEY( 64-1 downto 32);
    v2(PIPE_LENGTH-1)   <= IN_V2 xor IN_KEY( 96-1 downto 64);
    v3(PIPE_LENGTH-1)   <= IN_V3 xor IN_KEY(128-1 downto 96);

    -- ================================================
    --                     LOGIC
    -- ================================================

    -- generating another bit-shift of the seed if the key
    -- if unaligned.
    k2_g: if REMAIN > 0 generate
        process (all)
        begin
            if (seed_reg(PIPE_LENGTH-2)(127) = '1') then
                seed(PIPE_LENGTH-2) <= shift_left(seed_reg(PIPE_LENGTH-2), 1) xor to_unsigned(135, 128);
            else
                seed(PIPE_LENGTH-2) <= shift_left(seed_reg(PIPE_LENGTH-2), 1);
            end if;
        end process;

        v0(PIPE_LENGTH-2) <= v0_reg(PIPE_LENGTH-2);
        v1(PIPE_LENGTH-2) <= v1_reg(PIPE_LENGTH-2);
        v2(PIPE_LENGTH-2) <= v2_reg(PIPE_LENGTH-2);
        v3(PIPE_LENGTH-2) <= v3_reg(PIPE_LENGTH-2);
    end generate;

    -- combining state variables with the shifted seed.
    v0(ROUNDS+1)   <= v0_reg(ROUNDS+1) xor seed_reg(ROUNDS+1)( 32-1 downto  0);
    v1(ROUNDS+1)   <= v1_reg(ROUNDS+1) xor seed_reg(ROUNDS+1)( 64-1 downto 32);
    v2(ROUNDS+1)   <= v2_reg(ROUNDS+1) xor seed_reg(ROUNDS+1)( 96-1 downto 64);
    v3(ROUNDS+1)   <= v3_reg(ROUNDS+1) xor seed_reg(ROUNDS+1)(128-1 downto 96);
    seed(ROUNDS+1) <= seed_reg(ROUNDS+1);

    -- permutations of the state variables, number of generated
    -- permutations depends on the ROUNDS generic.
    round_g: for g in ROUNDS downto 1 generate
        process_block_round_i: entity work.CHASKEY_ROUND
        generic map (
            KEY_WIDTH  => 1,
            META_WIDTH => META_WIDTH,
            REG_SETUP  => ROUND_REG_SETUP
        ) port map (
            CLK        => CLK,
            RESET      => RESET,
            IN_KEY     => "0",
            IN_SEED    => seed_reg(g),
            IN_V0      => v0_reg(g),
            IN_V1      => v1_reg(g),
            IN_V2      => v2_reg(g),
            IN_V3      => v3_reg(g),
            IN_META    => meta(g),
            IN_VALID   => vld(g),
            OUT_SEED   => seed_reg(g-1),
            OUT_V0     => v0_reg(g-1),
            OUT_V1     => v1_reg(g-1),
            OUT_V2     => v2_reg(g-1),
            OUT_V3     => v3_reg(g-1),
            OUT_META   => meta(g-1),
            OUT_VALID  => vld(g-1)
        );
    end generate;

    -- final combination of the state variables with the shifted seed.
    v0(0) <= v0_reg(0) xor seed_reg(0)( 32-1 downto  0);
    v1(0) <= v1_reg(0) xor seed_reg(0)( 64-1 downto 32);
    v2(0) <= v2_reg(0) xor seed_reg(0)( 96-1 downto 64);
    v3(0) <= v3_reg(0) xor seed_reg(0)(128-1 downto 96);

    -- ================================================
    --                    PIPELINE
    -- ================================================
    -- generating registers between combinations and components.
    pipeline_g: for g in f_get_pipe_length(REMAIN)-1 downto 1 generate
        reg_g: if REG_SETUP(g) = '1' generate
            process (CLK)
            begin
                if rising_edge(CLK) then
                    seed_reg(PIPE_LENGTH-g-1) <= seed(PIPE_LENGTH-g);
                    meta(PIPE_LENGTH-g-1)     <= meta(PIPE_LENGTH-g);
                    vld(PIPE_LENGTH-g-1)      <= vld(PIPE_LENGTH-g);
                    v0_reg(PIPE_LENGTH-g-1)   <= v0(PIPE_LENGTH-g);
                    v1_reg(PIPE_LENGTH-g-1)   <= v1(PIPE_LENGTH-g);
                    v2_reg(PIPE_LENGTH-g-1)   <= v2(PIPE_LENGTH-g);
                    v3_reg(PIPE_LENGTH-g-1)   <= v3(PIPE_LENGTH-g);

                    if (RESET = '1') then
                        vld(PIPE_LENGTH-g-1)  <= '0';
                    end if;
                end if;
            end process;
        else generate
            seed_reg(PIPE_LENGTH-g-1) <= seed(PIPE_LENGTH-g);
            meta(PIPE_LENGTH-g-1)     <= meta(PIPE_LENGTH-g);
            vld(PIPE_LENGTH-g-1)      <= vld(PIPE_LENGTH-g);
            v0_reg(PIPE_LENGTH-g-1)   <= v0(PIPE_LENGTH-g);
            v1_reg(PIPE_LENGTH-g-1)   <= v1(PIPE_LENGTH-g);
            v2_reg(PIPE_LENGTH-g-1)   <= v2(PIPE_LENGTH-g);
            v3_reg(PIPE_LENGTH-g-1)   <= v3(PIPE_LENGTH-g);
        end generate;
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(0) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
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
        OUT_V0    <= v0(0);
        OUT_V1    <= v1(0);
        OUT_V2    <= v2(0);
        OUT_V3    <= v3(0);
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;

end architecture;
