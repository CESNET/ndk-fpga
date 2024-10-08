-- streaming_debug_probe_n.vhd: Data streaming interface debug probe (inverted logic).
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

entity STREAMING_DEBUG_PROBE_N is
  port(
    -- ===============
    -- Input interface
    -- ===============

    RX_SRC_RDY_N   : in  std_logic;
    RX_DST_RDY_N   : out std_logic;
    RX_SOP_N       : in  std_logic := '1';
    RX_EOP_N       : in  std_logic := '1';

    -- ================
    -- Output interface
    -- ================

    TX_SRC_RDY_N   : out std_logic;
    TX_DST_RDY_N   : in  std_logic;
    TX_SOP_N       : out std_logic := '1';
    TX_EOP_N       : out std_logic := '1';

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

architecture full of STREAMING_DEBUG_PROBE_N is
begin
  TX_SRC_RDY_N    <= DEBUG_DROP or DEBUG_BLOCK or RX_SRC_RDY_N;
  RX_DST_RDY_N    <= not DEBUG_DROP and (DEBUG_BLOCK or TX_DST_RDY_N);
  DEBUG_SRC_RDY   <= not DEBUG_BLOCK and not RX_SRC_RDY_N;
  DEBUG_DST_RDY   <= DEBUG_DROP or (not DEBUG_BLOCK and not TX_DST_RDY_N);
  TX_SOP_N        <= RX_SOP_N;
  TX_EOP_N        <= RX_EOP_N;
  DEBUG_SOP       <= not RX_SOP_N;
  DEBUG_EOP       <= not RX_EOP_N;
end architecture;

