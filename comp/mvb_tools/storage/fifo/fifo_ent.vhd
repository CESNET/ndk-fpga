-- fifo_ent.vhd: Multi-Value Bus generic FIFO
-- Copyright (C) 2016 CESNET z. s. p. o.
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;



entity MVB_FIFO is
  generic(
    ITEMS          : integer := 4; -- any possitive value
    ITEM_WIDTH     : integer := 8; -- any possitive value
    -- Usage of destination ready signaling. (When false, FIFO is not neaded at all!)
    USE_DST_RDY    : boolean := true;
    -- True => use BlockBAMs
    -- False => use SelectRAMs
    USE_BRAMS      : boolean := false;
    -- number of items in the FIFO
    FIFO_ITEMS     : integer := 64;
    -- Size of block (for LSTBLK signal)
    BLOCK_SIZE     : integer := 1;
    -- compute value of status signal
    STATUS_ENABLED : boolean := true;
    -- Ouptut register
    OUTPUT_REG     : boolean := true
  );
  port(
    CLK            : in std_logic;
    RESET          : in std_logic;

    RX_DATA       : in std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    RX_VLD        : in std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    TX_DATA       : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    TX_VLD        : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic;

    LSTBLK         : out std_logic;
    FULL           : out std_logic;
    EMPTY          : out std_logic;
    STATUS         : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
  );
end entity;
