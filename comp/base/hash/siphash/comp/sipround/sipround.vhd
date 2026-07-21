-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Subcomponent of the firmware implementation of the SIPHASH hash function.
--
-- Reference C implementation:
--     v0 += v1;
--     v1 = ROTL(v1, 13);
--     v1 ^= v0;
--     v0 = ROTL(v0, 32);
--     v2 += v3;
--     v3 = ROTL(v3, 16);
--     v3 ^= v2;
--     v0 += v3;
--     v3 = ROTL(v3, 21);
--     v3 ^= v0;
--     v2 += v1;
--     v1 = ROTL(v1, 17);
--     v1 ^= v2;
--     v2 = ROTL(v2, 32);
--
-- In the case of HalfSipHash, different constants in the rotations are used.
entity SIPROUND is
    generic (
        -- width of the whole key.
        KEY_WIDTH   : natural := 312;
        -- width of the passthrough metadata.
        META_WIDTH  : natural := 32;
        -- width of the words and internal state variables. Use 64 for full SipHash and
        -- 32 for HalfSipHash.
        WORD_WIDTH  : natural := 64;
        -- setup of the registers of this component.
        REG_SETUP   : std_logic_vector(4-1 downto 0) := "1111"
    );
    port (
        -- main clock
        CLK       : in  std_logic;
        -- synchronious reset.
        RESET     : in  std_logic;
        -- key passthrough input.
        IN_KEY    : in  unsigned(KEY_WIDTH-1 downto 0);
        -- internal state variables input.
        IN_V0     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V1     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V2     : in  unsigned(WORD_WIDTH-1 downto 0);
        IN_V3     : in  unsigned(WORD_WIDTH-1 downto 0);
        -- metadata input.
        IN_META   : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input.
        IN_VALID  : in  std_logic;

        -- key passthrough output.
        OUT_KEY   : out unsigned(KEY_WIDTH-1 downto 0);
        -- internal state variables output.
        OUT_V0    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V1    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V2    : out unsigned(WORD_WIDTH-1 downto 0);
        OUT_V3    : out unsigned(WORD_WIDTH-1 downto 0);
        -- metadata output.
        OUT_META  : out std_logic_vector(META_WIDTH-1 downto 0);
        -- valid passthrough.
        OUT_VALID : out std_logic
    );
end entity;

architecture FULL of SIPROUND is
    -- returns rotations constants, different for SipHash and HalfSipHash.
    function f_get_rotation_constants (word_width: natural) return n_array_t is
        variable rotation_const : n_array_t(0 to 5);
    begin
        case word_width is
            when 32 => rotation_const := (5,  8,  16, 13, 7,  16);
            when 64 => rotation_const := (13, 16, 32, 17, 21, 32);
            when others => null;
        end case;

        return rotation_const;
    end function;

    -- lengths of the rotations differ for based on the WORD_WIDTH
    constant ROTATION_CONST : n_array_t(0 to 5) := f_get_rotation_constants(WORD_WIDTH);
    -- length of the pipeline of this component
    constant PIPE_LENGTH    : natural           := 4;

    -- logic
    signal v0               : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v1               : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v2               : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v3               : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);

    -- registers
    signal key              : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal v0_reg           : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v1_reg           : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v2_reg           : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal v3_reg           : u_array_t(PIPE_LENGTH-1 downto 0)(WORD_WIDTH-1 downto 0);
    signal vld              : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta             : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key(3)    <= IN_KEY;
    v0_reg(3) <= IN_V0;
    v1_reg(3) <= IN_V1;
    v2_reg(3) <= IN_V2;
    v3_reg(3) <= IN_V3;
    vld(3)    <= IN_VALID;
    meta(3)   <= IN_META;

    -- ================================================
    --                     LOGIC
    -- ================================================

    v0(3) <= v0_reg(3) + v1_reg(3);
    v1(3) <= rotate_left(v1_reg(3), ROTATION_CONST(0));
    v2(3) <= v2_reg(3) + v3_reg(3);
    v3(3) <= rotate_left(v3_reg(3), ROTATION_CONST(1));

    v0(2) <= rotate_left(v0_reg(2), ROTATION_CONST(2));
    v1(2) <= v1_reg(2) xor v0_reg(2);
    v2(2) <= v2_reg(2);
    v3(2) <= v3_reg(2) xor v2_reg(2);

    v0(1) <= v0_reg(1) + v3_reg(1);
    v1(1) <= rotate_left(v1_reg(1), ROTATION_CONST(3));
    v2(1) <= v2_reg(1) + v1_reg(1);
    v3(1) <= rotate_left(v3_reg(1), ROTATION_CONST(4));

    v0(0) <= v0_reg(0);
    v1(0) <= v1_reg(0) xor v2_reg(0);
    v2(0) <= rotate_left(v2_reg(0), ROTATION_CONST(5));
    v3(0) <= v3_reg(0) xor v0_reg(0);

    -- ================================================
    --                    PIPELINE
    -- ================================================
    pipeline_g: for g in PIPE_LENGTH-1 downto 1 generate
        reg_g: if REG_SETUP(g) = '1' generate
            process (CLK)
            begin
                if rising_edge(CLK) then
                    key(g-1)        <= key(g);
                    v0_reg(g-1)     <= v0(g);
                    v1_reg(g-1)     <= v1(g);
                    v2_reg(g-1)     <= v2(g);
                    v3_reg(g-1)     <= v3(g);
                    meta(g-1)       <= meta(g);
                    vld(g-1)        <= vld(g);

                    if (RESET = '1') then
                        vld(g-1)    <= '0';
                    end if;
                end if;
            end process;
        else generate
            key(g-1)        <= key(g);
            v0_reg(g-1)     <= v0(g);
            v1_reg(g-1)     <= v1(g);
            v2_reg(g-1)     <= v2(g);
            v3_reg(g-1)     <= v3(g);
            meta(g-1)       <= meta(g);
            vld(g-1)        <= vld(g);
        end generate;
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(0) = '1' generate
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
