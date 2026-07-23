-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Processes Remainder of key of 15B in length and shorter in the SpookyHash algoritmhs.
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
        OUT_REG    : boolean := true
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
    -- width of the key in bytes used as padding. To ensure full compatibility, the calculation
    -- is performed with a 64 bit vector, even tho only bottom 8 bits are carried over.
    constant PADDING         : unsigned(64-1 downto 0) := to_unsigned(KEY_WIDTH / 8, 64);
    -- in case of zero remainder, the constant is "padded" by adding the length of the key
    constant PADDED_SC_CONST : unsigned(64-1 downto 0) := shift_left(PADDING, 56) + SC_CONST;

    -- padded remainder
    signal key                 : unsigned(128-1 downto 0);
    -- only h2 and h3 state variables are modified
    signal h2                  : unsigned(64-1 downto 0);
    signal h3                  : unsigned(64-1 downto 0);


begin
    -- zero-extension of remainder and padding the key
    key <= PADDING(8-1 downto 0) & resize(IN_KEY, 120);

    rem_g: if REMAINDER > 0 generate

        h2 <= IN_H2 + key( 64-1 downto  0);
        h3 <= IN_H3 + key(128-1 downto 64);

    else generate

        h2 <= IN_H2 + SC_CONST;
        h3 <= IN_H3 + PADDED_SC_CONST;

    end generate;

    -- ================================================
    --                     OUTPUT
    -- ================================================
    out_reg_g: if OUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                OUT_H0    <= IN_H0;
                OUT_H1    <= IN_H1;
                OUT_H2    <= h2;
                OUT_H3    <= h3;
                OUT_META  <= IN_META;
                OUT_VALID <= IN_VALID;

                if (RESET = '1') then
                    OUT_VALID <= '0';
                end if;
            end if;
        end process;
    else generate
        OUT_H0    <= IN_H0;
        OUT_H1    <= IN_H1;
        OUT_H2    <= h2;
        OUT_H3    <= h3;
        OUT_META  <= IN_META;
        OUT_VALID <= IN_VALID;
    end generate;

end architecture;
