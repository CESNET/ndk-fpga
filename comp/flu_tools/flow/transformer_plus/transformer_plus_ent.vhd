-- transformer_plus_ent.vhd: Entity of FrameLinkUnaligned Transformer component.
-- Copyright (C) 2013 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--            Roman Striz  <striz@netcope.com> channel support added
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
-- library containing log2 function
use work.math_pack.all;

entity FLU_TRANSFORMER_PLUS is
  generic(
    HEADER_WIDTH     : integer := 8;
    CHANNEL_WIDTH    : integer := 2;
    RX_DATA_WIDTH    : integer := 256;
    RX_SOP_POS_WIDTH : integer := 2;
    TX_DATA_WIDTH    : integer := 512;
    TX_SOP_POS_WIDTH : integer := 3
  );
  port(
    CLK            : in  std_logic;
    RESET          : in  std_logic;

    -- Frame Link Unaligned input interface
    RX_HEADER     : in std_logic_vector(HEADER_WIDTH-1 downto 0);
    RX_CHANNEL    : in std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    RX_DATA       : in std_logic_vector(RX_DATA_WIDTH-1 downto 0);
    RX_SOP_POS    : in std_logic_vector(max(1,RX_SOP_POS_WIDTH)-1 downto 0);
    RX_EOP_POS    : in std_logic_vector(max(1,log2(RX_DATA_WIDTH/8))-1 downto 0);
    RX_SOP        : in std_logic;
    RX_EOP        : in std_logic;
    RX_SRC_RDY    : in std_logic;
    RX_DST_RDY    : out std_logic;

    -- Frame Link Unaligned output interface
    TX_HEADER     : out std_logic_vector(HEADER_WIDTH-1 downto 0);
    TX_CHANNEL    : out std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    TX_DATA       : out std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    TX_SOP_POS    : out std_logic_vector(max(1,TX_SOP_POS_WIDTH)-1 downto 0);
    TX_EOP_POS    : out std_logic_vector(max(1,log2(TX_DATA_WIDTH/8))-1 downto 0);
    TX_SOP        : out std_logic;
    TX_EOP        : out std_logic;
    TX_SRC_RDY    : out std_logic;
    TX_DST_RDY    : in std_logic
  );
end entity;
