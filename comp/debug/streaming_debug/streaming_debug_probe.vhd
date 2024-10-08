-- streaming_debug_probe.vhd: Data streaming interface debug probe.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

entity STREAMING_DEBUG_PROBE is
  port(
    -- ===============
    -- Input interface
    -- ===============

    RX_SRC_RDY     : in  std_logic;
    RX_DST_RDY     : out std_logic;
    RX_SOP         : in  std_logic := '0';
    RX_EOP         : in  std_logic := '0';

    -- ================
    -- Output interface
    -- ================

    TX_SRC_RDY     : out std_logic;
    TX_DST_RDY     : in  std_logic;
    TX_SOP         : out std_logic := '0';
    TX_EOP         : out std_logic := '0';

    -- ==================
    -- Debuging interface
    -- ==================

    -- blocks data words on pipe's input interface
    DEBUG_BLOCK        : in  std_logic := '0';
    -- drops data words on pipe's input interface (higher priority than BLOCK)
    DEBUG_DROP         : in  std_logic := '0';
    -- source ready on pipe's input interface
    DEBUG_SRC_RDY      : out std_logic;
    -- destination ready on pipe's input interface
    DEBUG_DST_RDY      : out std_logic;
    -- start of transaction on pipe's input interface
    DEBUG_SOP          : out std_logic := '0';
    -- end of transaction on pipe's input interface
    DEBUG_EOP          : out std_logic := '0'
  );
end entity;

architecture full of STREAMING_DEBUG_PROBE is
begin
  TX_SRC_RDY      <= not DEBUG_DROP and not DEBUG_BLOCK and RX_SRC_RDY;
  RX_DST_RDY      <= DEBUG_DROP or (not DEBUG_BLOCK and TX_DST_RDY);
  DEBUG_SRC_RDY   <= not DEBUG_BLOCK and RX_SRC_RDY;
  DEBUG_DST_RDY   <= DEBUG_DROP or (not DEBUG_BLOCK and TX_DST_RDY);
  TX_SOP          <= RX_SOP;
  TX_EOP          <= RX_EOP;
  DEBUG_SOP       <= RX_SOP;
  DEBUG_EOP       <= RX_EOP;
end architecture;

