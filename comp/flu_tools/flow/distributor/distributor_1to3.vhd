--
-- distributor_1to3.vhd: Three port wrapper for distributor component for Frame Link Unaligned
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
entity FLU_DISTRIBUTOR_1TO3 is
   generic(
       DATA_WIDTH:    integer:=256;
       SOP_POS_WIDTH: integer:=2
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

      -- Frame Link Unaligned output interfaces
      -- Interface 0
      TX0_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX0_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX0_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX0_SOP        : out std_logic;
      TX0_EOP        : out std_logic;
      TX0_SRC_RDY    : out std_logic;
      TX0_DST_RDY    : in std_logic;

      -- Interface 1
      TX1_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX1_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX1_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX1_SOP        : out std_logic;
      TX1_EOP        : out std_logic;
      TX1_SRC_RDY    : out std_logic;
      TX1_DST_RDY    : in std_logic;

      -- Interface 2
      TX2_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX2_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX2_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX2_SOP        : out std_logic;
      TX2_EOP        : out std_logic;
      TX2_SRC_RDY    : out std_logic;
      TX2_DST_RDY    : in std_logic;

      -- Distribution control interface
      INUM_MASK     : in std_logic_vector(3-1 downto 0);
      INUM_READY    : in std_logic;
      INUM_NEXT     : out std_logic
     );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture ARCH of FLU_DISTRIBUTOR_1TO3 is

constant OUTPUT_PORTS:  integer:=3;
constant EOP_POS_WIDTH: integer:=log2(DATA_WIDTH/8);
signal data    : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal eop_pos : std_logic_vector(OUTPUT_PORTS*EOP_POS_WIDTH-1 downto 0);
signal sop_pos : std_logic_vector(OUTPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
signal sop     : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal eop     : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal src_rdy : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal dst_rdy : std_logic_vector(OUTPUT_PORTS-1 downto 0);

begin
-- FLU_DISTRIBUTOR entity instance
   flu_distributor_i: entity work.FLU_DISTRIBUTOR
   generic map(
      DATA_WIDTH    => DATA_WIDTH,
      SOP_POS_WIDTH => SOP_POS_WIDTH,
      OUTPUT_PORTS  => OUTPUT_PORTS
   )
   port map(
      RESET=>RESET,
      CLK=>CLK,

      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,

      TX_DATA       => data,
      TX_SOP_POS    => sop_pos,
      TX_EOP_POS    => eop_pos,
      TX_SOP        => sop,
      TX_EOP        => eop,
      TX_SRC_RDY    => src_rdy,
      TX_DST_RDY    => dst_rdy,

      INUM_MASK     => INUM_MASK,
      INUM_READY    => INUM_READY,
      INUM_NEXT     => INUM_NEXT
   );

   -- Interface 0
   TX0_DATA     <= data((0+1)*DATA_WIDTH-1 downto 0*DATA_WIDTH);
   TX0_SOP_POS  <= sop_pos((0+1)*SOP_POS_WIDTH-1 downto 0*SOP_POS_WIDTH);
   TX0_EOP_POS  <= eop_pos((0+1)*EOP_POS_WIDTH-1 downto 0*EOP_POS_WIDTH);
   TX0_SOP      <= sop(0);
   TX0_EOP      <= eop(0);
   TX0_SRC_RDY  <= src_rdy(0);
   dst_rdy(0)   <= TX0_DST_RDY;
   -- Interface 1
   TX1_DATA     <= data((1+1)*DATA_WIDTH-1 downto 1*DATA_WIDTH);
   TX1_SOP_POS  <= sop_pos((1+1)*SOP_POS_WIDTH-1 downto 1*SOP_POS_WIDTH);
   TX1_EOP_POS  <= eop_pos((1+1)*EOP_POS_WIDTH-1 downto 1*EOP_POS_WIDTH);
   TX1_SOP      <= sop(1);
   TX1_EOP      <= eop(1);
   TX1_SRC_RDY  <= src_rdy(1);
   dst_rdy(1)   <= TX1_DST_RDY;
   -- Interface 2
   TX2_DATA     <= data((2+1)*DATA_WIDTH-1 downto 2*DATA_WIDTH);
   TX2_SOP_POS  <= sop_pos((2+1)*SOP_POS_WIDTH-1 downto 2*SOP_POS_WIDTH);
   TX2_EOP_POS  <= eop_pos((2+1)*EOP_POS_WIDTH-1 downto 2*EOP_POS_WIDTH);
   TX2_SOP      <= sop(2);
   TX2_EOP      <= eop(2);
   TX2_SRC_RDY  <= src_rdy(2);
   dst_rdy(2)   <= TX2_DST_RDY;

end architecture;
