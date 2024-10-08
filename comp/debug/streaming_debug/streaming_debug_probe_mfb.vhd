-- streaming_debug_probe_mfb.vhd: Data streaming interface debug probe.
-- Copyright (C) 2023 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity STREAMING_DEBUG_PROBE_MFB is
    generic (
        -- Number of MFB regions.
        REGIONS : natural := 4
    );
    port(
        -- ===============
        -- Input interface
        -- ===============
        RX_SRC_RDY     : in  std_logic;
        RX_DST_RDY     : out std_logic;
        RX_SOF         : in  std_logic_vector(REGIONS-1 downto 0) := (others => '0');
        RX_EOF         : in  std_logic_vector(REGIONS-1 downto 0) := (others => '0');

        -- ================
        -- Output interface
        -- ================
        TX_SRC_RDY     : out std_logic;
        TX_DST_RDY     : in  std_logic;
        TX_SOF         : out std_logic_vector(REGIONS-1 downto 0) := (others => '0');
        TX_EOF         : out std_logic_vector(REGIONS-1 downto 0) := (others => '0');

        -- ==================
        -- Debuging interface
        -- ==================
        -- blocks data words on pipe's input interface
        DEBUG_BLOCK    : in  std_logic := '0';
        -- drops data words on pipe's input interface (higher priority than BLOCK)
        DEBUG_DROP     : in  std_logic := '0';
        -- source ready on pipe's input interface
        DEBUG_SRC_RDY  : out std_logic;
        -- destination ready on pipe's input interface
        DEBUG_DST_RDY  : out std_logic;
        -- start of transaction on pipe's input interface
        DEBUG_SOF      : out std_logic_vector(REGIONS-1 downto 0) := (others => '0');
        -- end of transaction on pipe's input interface
        DEBUG_EOF      : out std_logic_vector(REGIONS-1 downto 0) := (others => '0')
    );
end entity;

architecture FULL of STREAMING_DEBUG_PROBE_MFB is
begin
    TX_SRC_RDY    <= not DEBUG_DROP and not DEBUG_BLOCK and RX_SRC_RDY;
    RX_DST_RDY    <= DEBUG_DROP or (not DEBUG_BLOCK and TX_DST_RDY);
    DEBUG_SRC_RDY <= not DEBUG_BLOCK and RX_SRC_RDY;
    DEBUG_DST_RDY <= DEBUG_DROP or (not DEBUG_BLOCK and TX_DST_RDY);
    TX_SOF        <= RX_SOF;
    TX_EOF        <= RX_EOF;
    DEBUG_SOF     <= RX_SOF;
    DEBUG_EOF     <= RX_EOF;
end architecture;
