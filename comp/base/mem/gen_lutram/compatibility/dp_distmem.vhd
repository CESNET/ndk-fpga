-- dp_distmem.vhd: Compatibility wrapper of GEN_LUTRAM
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- WARNING:
-- Do not use this memory in new components, use GEN_LUTRAM!!!
-- This is just a wrapper for backward compatibility.

entity DP_DISTMEM is
    generic(
        DATA_WIDTH : integer := 21; -- any possitive value
        ITEMS      : integer := 64; -- any possitive value
        DEVICE     : string  := "7SERIES" -- target device: "7SERIES", "ULTRASCALE", "ARRIA10", "STRATIX10".
    );
    port(
        DI    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        WE    : in  std_logic;
        WCLK  : in  std_logic;
        ADDRA : in  std_logic_vector(LOG2(ITEMS)-1 downto 0);
        DOA   : out std_logic_vector(DATA_WIDTH-1 downto 0);
        ADDRB : in  std_logic_vector(LOG2(ITEMS)-1 downto 0);
        DOB   : out std_logic_vector(DATA_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of DP_DISTMEM is

    signal rd_addr : std_logic_vector(2*log2(ITEMS)-1 downto 0);
    signal rd_data : std_logic_vector(2*DATA_WIDTH-1 downto 0);

begin

    rd_addr <= ADDRB & ADDRA;

    gen_lutram_i : entity work.GEN_LUTRAM
    generic map (
        DATA_WIDTH         => DATA_WIDTH,
        ITEMS              => ITEMS,
        RD_PORTS           => 2,
        RD_LATENCY         => 0,
        WRITE_USE_RD_ADDR0 => True,
        MLAB_CONSTR_RDW_DC => True,
        DEVICE             => DEVICE
    )
    port map (
        CLK     => WCLK,
        WR_EN   => WE,
        WR_ADDR => (others => '0'),
        WR_DATA => DI,
        RD_ADDR => rd_addr,
        RD_DATA => rd_data
    );

    DOA <= rd_data(1*DATA_WIDTH-1 downto 0*DATA_WIDTH);
    DOB <= rd_data(2*DATA_WIDTH-1 downto 1*DATA_WIDTH);

end architecture;
