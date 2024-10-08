-- trimming_unit_flu_ent.vhd: Trimming unit for FLU entity
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id:$
--
-- TODO:
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: TRIMMING_UNIT_FLU
-- ----------------------------------------------------------------------------
entity TRIMMING_UNIT_FLU is
   generic
   (
      DATA_WIDTH      : integer := 512;
      SOP_POS_WIDTH   : integer := 2;
      LENGTH_WIDTH    : integer := 12
   );
   port(
      -- common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Control Interface
      LENGTH         : in std_logic_vector(LENGTH_WIDTH-1 downto 0);
      LENGTH_READY   : in std_logic;
      LENGTH_NEXT    : out std_logic;

      -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Frame Link Unaligned output interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity TRIMMING_UNIT_FLU;


