--
-- binder_ent.vhd: Binder 2-1 component for Frame Link Unaligned
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

-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_BINDER_2TO1 is
   generic(
       DATA_WIDTH:    integer:=256;
       SOP_POS_WIDTH: integer:=2
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame Link Unaligned input interface
      RX0_DATA      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX0_SOP_POS   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX0_EOP_POS   : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX0_SOP       : in std_logic;
      RX0_EOP       : in std_logic;
      RX0_SRC_RDY   : in std_logic;
      RX0_DST_RDY   : out std_logic;

      -- Frame Link Unaligned input interface
      RX1_DATA      : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX1_SOP_POS   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX1_EOP_POS   : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX1_SOP       : in std_logic;
      RX1_EOP       : in std_logic;
      RX1_SRC_RDY   : in std_logic;
      RX1_DST_RDY   : out std_logic;

      -- Frame Link Unaligned concentrated interface
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH of FLU_BINDER_2TO1 is
   constant INPUT_PORTS   : integer:=2;
   constant EOP_POS_WIDTH : integer:=log2(DATA_WIDTH/8);
   signal data    : std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
   signal eop_pos : std_logic_vector(INPUT_PORTS*EOP_POS_WIDTH-1 downto 0);
   signal sop_pos : std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
   signal sop     : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal eop     : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal src_rdy : std_logic_vector(INPUT_PORTS-1 downto 0);
   signal dst_rdy : std_logic_vector(INPUT_PORTS-1 downto 0);

begin
  flu_binder: entity work.FLU_BINDER
  generic map(
       DATA_WIDTH=>DATA_WIDTH,
       SOP_POS_WIDTH=>SOP_POS_WIDTH,
       INPUT_PORTS=>INPUT_PORTS
   )
   port map(
       -- Common interface
      RESET=>RESET,
      CLK=>CLK,

      -- Frame Link Unaligned input interface
      RX_DATA       => data,
      RX_SOP_POS    => sop_pos,
      RX_EOP_POS    => eop_pos,
      RX_SOP        => sop,
      RX_EOP        => eop,
      RX_SRC_RDY    => src_rdy,
      RX_DST_RDY    => dst_rdy,

      -- Frame Link Unaligned output interfaces
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY
   );

   data        <= RX1_DATA    & RX0_DATA;
   sop_pos     <= RX1_SOP_POS & RX0_SOP_POS;
   eop_pos     <= RX1_EOP_POS & RX0_EOP_POS;
   sop         <= RX1_SOP     & RX0_SOP;
   eop         <= RX1_EOP     & RX0_EOP;
   src_rdy     <= RX1_SRC_RDY & RX0_SRC_RDY;
   RX1_DST_RDY <= dst_rdy(1);
   RX0_DST_RDY <= dst_rdy(0);

end architecture;
