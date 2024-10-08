-- distributor_ent.vhd: Frame Link Unaligned 1-n distributor entity.
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity flu_distributor is
   generic(
      DATA_WIDTH:    integer:=256;
      SOP_POS_WIDTH: integer:=2;
      OUTPUT_PORTS:  integer:=2
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame Link Unaligned input interface
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(OUTPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(OUTPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_EOP        : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_SRC_RDY    : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_DST_RDY    : in std_logic_vector(OUTPUT_PORTS-1 downto 0);

      -- Distribution control interface
      INUM_MASK     : in std_logic_vector(OUTPUT_PORTS-1 downto 0);
      INUM_READY    : in std_logic;
      INUM_NEXT     : out std_logic
   );
end entity flu_distributor;

