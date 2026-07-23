-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Processes 32B chunks of key in the SpookyHash algoritmhs.
entity SPOOKY_SETS is
    generic (
        -- true for Sets32, false for Sets16
        SETS_TYPE  : boolean := true;
        -- width of the whole key
        KEY_WIDTH  : natural := 256;
        -- width of the passthrough metadata
        META_WIDTH : natural := 32;
        -- key offset in bits
        KEY_OFFSET : natural := 0;
        -- setup of the registers of this component. If SETS_TYPE is set to
        -- false, most significant bit is ignored
        REG_SETUP  : std_logic_vector(27-1 downto 0) := "111111111111111111111111111"
    );
    port (
        -- main clock
        CLK        : in std_logic;
        -- synchronious reset
        RESET      : in std_logic;

        -- whole key to be hashed
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

architecture FULL of SPOOKY_SETS is
    -- length of the pipeline of this component
    constant PIPE_LENGTH : natural := 3;

    -- logic
    signal key           : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal h0            : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1            : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2            : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3            : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal vld           : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta          : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

    -- registers
    signal key_reg       : u_array_t(PIPE_LENGTH-1 downto 0)(KEY_WIDTH-1 downto 0);
    signal h0_reg        : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1_reg        : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2_reg        : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3_reg        : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal vld_reg       : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta_reg      : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key_reg(2)  <= IN_KEY;
    h0_reg(2)   <= IN_H0;
    h1_reg(2)   <= IN_H1;
    h2_reg(2)   <= IN_H2;
    h3_reg(2)   <= IN_H3;
    meta_reg(2) <= IN_META;
    vld_reg(2)  <= IN_VALID;

    -- ================================================
    --                     LOGIC
    -- ================================================

    -- c += u.p64[0]; d += u.p64[1];
    key(2)  <= key_reg(2);
    h0(2)   <= h0_reg(2);
    h1(2)   <= h1_reg(2);
    h2(2)   <= h2_reg(2) + key_reg(2)(KEY_OFFSET+64-1 downto KEY_OFFSET);
    h3(2)   <= h3_reg(2) + key_reg(2)(KEY_OFFSET+128-1 downto KEY_OFFSET+64);
    meta(2) <= meta_reg(2);
    vld(2)  <= vld_reg(2);

    shortmix_i: entity work.SPOOKY_SHORTMIX
    generic map (
        KEY_WIDTH  => KEY_WIDTH,
        META_WIDTH => META_WIDTH,
        REG_SETUP  => REG_SETUP(26-1 downto 1)
    ) port map (
        CLK       => CLK,
        RESET     => RESET,
        IN_KEY    => key(2),
        IN_H0     => h0(2),
        IN_H1     => h1(2),
        IN_H2     => h2(2),
        IN_H3     => h3(2),
        IN_META   => meta(2),
        IN_VALID  => vld(2),
        OUT_KEY   => key(1),
        OUT_H0    => h0(1),
        OUT_H1    => h1(1),
        OUT_H2    => h2(1),
        OUT_H3    => h3(1),
        OUT_META  => meta(1),
        OUT_VALID => vld(1)
    );

    sets_type_g: if SETS_TYPE generate
        -- a += u.p64[2]; b += u.p64[3];
        key(0)  <= key_reg(0);
        h0(0)   <= h0_reg(0) + key_reg(0)(KEY_OFFSET+192-1 downto KEY_OFFSET+128);
        h1(0)   <= h1_reg(0) + key_reg(0)(KEY_OFFSET+256-1 downto KEY_OFFSET+192);
        h2(0)   <= h2_reg(0);
        h3(0)   <= h3_reg(0);
        meta(0) <= meta_reg(0);
        vld(0)  <= vld_reg(0);
    else generate
        key(0)  <= key_reg(0);
        h0(0)   <= h0_reg(0);
        h1(0)   <= h1_reg(0);
        h2(0)   <= h2_reg(0);
        h3(0)   <= h3_reg(0);
        meta(0) <= meta_reg(0);
        vld(0)  <= vld_reg(0);
    end generate;

    -- ================================================
    --                    PIPELINE
    -- ================================================
    -- generates register if is sets32 and the coresponding
    -- bit is set to true
    reg_g: if SETS_TYPE and REG_SETUP(26) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                key_reg(0)  <= key(1);
                h0_reg(0)   <= h0(1);
                h1_reg(0)   <= h1(1);
                h2_reg(0)   <= h2(1);
                h3_reg(0)   <= h3(1);
                meta_reg(0) <= meta(1);
                vld_reg(0)  <= vld(1);

                if (RESET = '1') then
                    vld_reg(0) <= '0';
                end if;
            end if;
        end process;
    else generate
        key_reg(0)  <= key(1);
        h0_reg(0)   <= h0(1);
        h1_reg(0)   <= h1(1);
        h2_reg(0)   <= h2(1);
        h3_reg(0)   <= h3(1);
        meta_reg(0) <= meta(1);
        vld_reg(0)  <= vld(1);
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(0) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_KEY   <= key(0);
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
        OUT_KEY   <= key(0);
        OUT_H0    <= h0(0);
        OUT_H1    <= h1(0);
        OUT_H2    <= h2(0);
        OUT_H3    <= h3(0);
        OUT_META  <= meta(0);
        OUT_VALID <= vld(0);
    end generate;

end architecture;
