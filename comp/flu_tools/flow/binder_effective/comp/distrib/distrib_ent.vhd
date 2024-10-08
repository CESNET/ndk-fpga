--
-- distrib_ent.vhd: FLU Frame RR distributor
-- Copyright (C) 2014 CESNET
-- Author:  Pavel Benacek  <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity DISTRIB is
   generic(
       --! FLU protocol generics
       DATA_WIDTH    : integer:= 256;
       SOP_POS_WIDTH : integer:= 2
   );
   port(
       -- -------------------------------------------------
       -- \name Common interface
       -- -------------------------------------------------
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- --------------------------------------------------
      -- \name Frame Link Unaligned input interface
      -- --------------------------------------------------
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- Distributed to output (active when SOP = 1)
      DISTRIBUTED_TO : out std_logic;

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface (lane 0)
      -- --------------------------------------------------
      TX_DATA0      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS0   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS0   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP0       : out std_logic;
      TX_EOP0       : out std_logic;
      TX_SRC_RDY0   : out std_logic;
      TX_DST_RDY0   : in std_logic;

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface (lane 1)
      -- --------------------------------------------------
      TX_DATA1      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS1   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS1   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP1       : out std_logic;
      TX_EOP1       : out std_logic;
      TX_SRC_RDY1   : out std_logic;
      TX_DST_RDY1   : in std_logic
   );
end entity;
