-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Processes remainder of key of 15B in length and shorter in the spookyhash algoritmhs.
entity SPOOKY_REMAINDER is
    generic (
        -- width of the whole key
        KEY_WIDTH  : natural := 256;
        -- width of the passthrough metadata
        META_WIDTH : natural := 32;
        -- width of the key remainder in bytes
        REMAINDER  : natural := 15;
        -- constant used in spookyhash algorithm
        SC_CONST   : unsigned(64-1 downto 0) := X"DEADBEEFDEADBEEF";
        -- setup of the registers of this component
        REG_SETUP  : std_logic_vector(5-1 downto 0) := "11111"
    );
    port (
        -- main clock
        CLK        : in std_logic;
        -- synchronious reset
        RESET      : in std_logic;

        -- key remainder
        IN_KEY     : in  unsigned(REMAINDER*8-1 downto 0);
        -- variables used in hash calculation
        IN_H0      : in  unsigned(64-1 downto 0);
        IN_H1      : in  unsigned(64-1 downto 0);
        IN_H2      : in  unsigned(64-1 downto 0);
        IN_H3      : in  unsigned(64-1 downto 0);
        -- metadata input
        IN_META    : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- validity of input
        IN_VALID   : in  std_logic;

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

architecture FULL of SPOOKY_REMAINDER is
    -- returns length of the pipeline based on the length of the key remainder
    function f_calc_pipe_length (remainder: natural) return natural is
    begin
        case remainder is
            when 15     => return 5;
            when 14     => return 4;
            when 13     => return 3;
            when 12     => return 2;
            when 11     => return 5;
            when 10     => return 4;
            when 9      => return 3;
            when 8      => return 2;
            when 7      => return 5;
            when 6      => return 4;
            when 5      => return 3;
            when 4      => return 2;
            when 3      => return 4;
            when 2      => return 3;
            when 1      => return 2;
            when 0      => return 2;
            when others => return 0;
        end case;
    end function;

    -- length of the pipeline of this component
    constant PIPE_LENGTH       : natural := f_calc_pipe_length(REMAINDER);
    -- shifted width of the key used in the algorithm
    constant SHIFTED_KEY_WIDTH : unsigned(64-1 downto 0) := shift_left(to_unsigned(KEY_WIDTH / 8, 64), 56);

    -- logic
    signal h2                  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3                  : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);

    -- registers
    signal key_reg             : u_array_t(PIPE_LENGTH-1 downto 0)(REMAINDER*8-1 downto 0);
    signal h0_reg              : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h1_reg              : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h2_reg              : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);
    signal h3_reg              : u_array_t(PIPE_LENGTH-1 downto 0)(64-1 downto 0);

    signal vld_reg             : std_logic_vector(PIPE_LENGTH-1 downto 0);
    signal meta_reg            : slv_array_t(PIPE_LENGTH-1 downto 0)(META_WIDTH-1 downto 0);

begin
    -- ================================================
    --                      INPUT
    -- ================================================
    key_reg(PIPE_LENGTH-1)  <= IN_KEY;
    h0_reg(PIPE_LENGTH-1)   <= IN_H0;
    h1_reg(PIPE_LENGTH-1)   <= IN_H1;
    h2_reg(PIPE_LENGTH-1)   <= IN_H2;
    h3_reg(PIPE_LENGTH-1)   <= IN_H3;
    vld_reg(PIPE_LENGTH-1)  <= IN_VALID;
    meta_reg(PIPE_LENGTH-1) <= IN_META;

    -- ================================================
    --                     LOGIC
    -- ================================================

    h2(PIPE_LENGTH-1) <= h2_reg(PIPE_LENGTH-1);
    h3(PIPE_LENGTH-1) <= h3_reg(PIPE_LENGTH-1) + SHIFTED_KEY_WIDTH;

    -- handle the last 0..15 bytes, and its length
    rem_g: if REMAINDER >= 12 generate
        rem15_g: if REMAINDER = 15 generate
            h2(3) <= h2_reg(3);
            h3(3) <= h3_reg(3) + (shift_left((56-1 downto 0 => '0') & key_reg(3)(120-1 downto 112), 48));
        end generate;

        rem14_g: if REMAINDER >= 14 generate
            h2(2) <= h2_reg(2);
            h3(2) <= h3_reg(2) + (shift_left((56-1 downto 0 => '0') & key_reg(2)(112-1 downto 104), 40));
        end generate;

        rem13_g: if REMAINDER >= 13 generate
            h2(1) <= h2_reg(1);
            h3(1) <= h3_reg(1) + (shift_left((56-1 downto 0 => '0') & key_reg(1)(104-1 downto 96), 32));
        end generate;

        h2(0) <= h2_reg(0) + key_reg(0)(64-1 downto 0);
        h3(0) <= h3_reg(0) + ((32-1 downto 0 => '0') & key_reg(0)(96-1 downto 64));

    elsif REMAINDER >= 8 and REMAINDER < 12 generate
        rem11_g: if REMAINDER = 11 generate
            h2(3) <= h2_reg(3);
            h3(3) <= h3_reg(3) + (shift_left((56-1 downto 0 => '0') & key_reg(3)(88-1 downto 80), 16));
        end generate;

        rem10_g: if REMAINDER >= 10 generate
            h2(2) <= h2_reg(2);
            h3(2) <= h3_reg(2) + (shift_left((56-1 downto 0 => '0') & key_reg(2)(80-1 downto 72), 8));
        end generate;

        rem9_g: if REMAINDER >= 9 generate
            h2(1) <= h2_reg(1);
            h3(1) <= h3_reg(1) + ((56-1 downto 0 => '0') & key_reg(1)(72-1 downto 64));
        end generate;

        h2(0) <= h2_reg(0) + key_reg(0)(64-1 downto 0);
        h3(0) <= h3_reg(0);

    elsif REMAINDER >= 4 and REMAINDER < 8 generate
        rem7_g: if REMAINDER = 7 generate
            h2(3) <= h2_reg(3) + (shift_left((56-1 downto 0 => '0') & key_reg(3)(56-1 downto 48), 48));
            h3(3) <= h3_reg(3);
        end generate;

        rem6_g: if REMAINDER >= 6 generate
            h2(2) <= h2_reg(2) + (shift_left((56-1 downto 0 => '0') & key_reg(2)(48-1 downto 40), 40));
            h3(2) <= h3_reg(2);
        end generate;

        rem5_g: if REMAINDER >= 5 generate
            h2(1) <= h2_reg(1) + (shift_left((56-1 downto 0 => '0') & key_reg(1)(40-1 downto 32), 32));
            h3(1) <= h3_reg(1);
        end generate;

        h2(0) <= h2_reg(0) + ((32-1 downto 0 => '0') & key_reg(0)(32-1 downto 0));
        h3(0) <= h3_reg(0);

    elsif REMAINDER >= 1 and REMAINDER < 4 generate
        rem3_g: if REMAINDER = 3 generate
            h2(2) <= h2_reg(2) + (shift_left((56-1 downto 0 => '0') & key_reg(2)(24-1 downto 16), 16));
            h3(2) <= h3_reg(2);
        end generate;

        rem2_g: if REMAINDER >= 2 generate
            h2(1) <= h2_reg(1) + (shift_left((56-1 downto 0 => '0') & key_reg(1)(16-1 downto 8), 8));
            h3(1) <= h3_reg(1);
        end generate;

        h2(0) <= h2_reg(0) + ((56-1 downto 0 => '0') & key_reg(0)(8-1 downto 0));
        h3(0) <= h3_reg(0);

    else generate
        h2(0) <= h2_reg(0) + SC_CONST;
        h3(0) <= h3_reg(0) + SC_CONST;
    end generate;

    -- ================================================
    --                    PIPELINE
    -- ================================================
    pipeline_g: for g in PIPE_LENGTH-1 downto 1 generate
        reg_g: if REG_SETUP(g) = '1' generate
            process (CLK)
            begin
                if rising_edge(CLK) then
                    key_reg(g-1)  <= key_reg(g);
                    h0_reg(g-1)   <= h0_reg(g);
                    h1_reg(g-1)   <= h1_reg(g);
                    h2_reg(g-1)   <= h2(g);
                    h3_reg(g-1)   <= h3(g);
                    meta_reg(g-1) <= meta_reg(g);
                    vld_reg(g-1)  <= vld_reg(g);

                    if (RESET = '1') then
                        vld_reg(g-1) <= '0';
                    end if;
                end if;
            end process;
        else generate
            key_reg(g-1)  <= key_reg(g);
            h0_reg(g-1)   <= h0_reg(g);
            h1_reg(g-1)   <= h1_reg(g);
            h2_reg(g-1)   <= h2(g);
            h3_reg(g-1)   <= h3(g);
            meta_reg(g-1) <= meta_reg(g);
            vld_reg(g-1)  <= vld_reg(g);
        end generate;
    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if REG_SETUP(0) = '1' generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_H0    <= h0_reg(0);
                OUT_H1    <= h1_reg(0);
                OUT_H2    <= h2(0);
                OUT_H3    <= h3(0);
                OUT_META  <= meta_reg(0);
                OUT_VALID <= vld_reg(0);

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_H0    <= h0_reg(0);
        OUT_H1    <= h1_reg(0);
        OUT_H2    <= h2(0);
        OUT_H3    <= h3(0);
        OUT_META  <= meta_reg(0);
        OUT_VALID <= vld_reg(0);
    end generate;

end architecture;
