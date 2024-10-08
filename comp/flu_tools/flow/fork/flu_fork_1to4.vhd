--
-- flu_fork_1to4.vhd: Four port wrapper for fork component for Frame Link Unaligned
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
entity FLU_FORK_1TO4 is
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

      -- Interface 3
      TX3_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX3_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX3_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX3_SOP        : out std_logic;
      TX3_EOP        : out std_logic;
      TX3_SRC_RDY    : out std_logic;
      TX3_DST_RDY    : in std_logic
     );
end entity FLU_FORK_1TO4;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FLU_FORK_1TO4_ARCH of FLU_FORK_1TO4 is

constant OUTPUT_PORTS:  integer:=4;
constant EOP_POS_WIDTH: integer:=log2(DATA_WIDTH/8);
signal data    : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal eop_pos : std_logic_vector(OUTPUT_PORTS*EOP_POS_WIDTH-1 downto 0);
signal sop_pos : std_logic_vector(OUTPUT_PORTS*SOP_POS_WIDTH-1 downto 0);

begin
-- FLU_FORK entity instance
  flu_fork: entity work.FLU_FORK
  generic map(
       DATA_WIDTH=>DATA_WIDTH,
       SOP_POS_WIDTH=>SOP_POS_WIDTH,
       OUTPUT_PORTS=>OUTPUT_PORTS
   )
   port map(
       -- Common interface
      RESET=>RESET,
      CLK=>CLK,

      -- Frame Link Unaligned input interface
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,

      -- Frame Link Unaligned output interfaces
      TX_DATA          => data,
      TX_SOP_POS       => sop_pos,
      TX_EOP_POS       => eop_pos,
      TX_SOP(0)        => TX0_SOP,
      TX_SOP(1)        => TX1_SOP,
      TX_SOP(2)        => TX2_SOP,
      TX_SOP(3)        => TX3_SOP,
      TX_EOP(0)        => TX0_EOP,
      TX_EOP(1)        => TX1_EOP,
      TX_EOP(2)        => TX2_EOP,
      TX_EOP(3)        => TX3_EOP,
      TX_SRC_RDY(0)    => TX0_SRC_RDY,
      TX_SRC_RDY(1)    => TX1_SRC_RDY,
      TX_SRC_RDY(2)    => TX2_SRC_RDY,
      TX_SRC_RDY(3)    => TX3_SRC_RDY,
      TX_DST_RDY(0)    => TX0_DST_RDY,
      TX_DST_RDY(1)    => TX1_DST_RDY,
      TX_DST_RDY(2)    => TX2_DST_RDY,
      TX_DST_RDY(3)    => TX3_DST_RDY
     );

     -- Interface 0
     TX0_DATA    <= data((0+1)*DATA_WIDTH-1 downto 0*DATA_WIDTH);
     TX0_SOP_POS <= sop_pos((0+1)*SOP_POS_WIDTH-1 downto 0*SOP_POS_WIDTH);
     TX0_EOP_POS <= eop_pos((0+1)*EOP_POS_WIDTH-1 downto 0*EOP_POS_WIDTH);
     -- Interface 1
     TX1_DATA    <= data((1+1)*DATA_WIDTH-1 downto 1*DATA_WIDTH);
     TX1_SOP_POS <= sop_pos((1+1)*SOP_POS_WIDTH-1 downto 1*SOP_POS_WIDTH);
     TX1_EOP_POS <= eop_pos((1+1)*EOP_POS_WIDTH-1 downto 1*EOP_POS_WIDTH);
     -- Interface 2
     TX1_DATA    <= data((2+1)*DATA_WIDTH-1 downto 2*DATA_WIDTH);
     TX1_SOP_POS <= sop_pos((2+1)*SOP_POS_WIDTH-1 downto 2*SOP_POS_WIDTH);
     TX1_EOP_POS <= eop_pos((2+1)*EOP_POS_WIDTH-1 downto 2*EOP_POS_WIDTH);
     -- Interface 3
     TX1_DATA    <= data((3+1)*DATA_WIDTH-1 downto 3*DATA_WIDTH);
     TX1_SOP_POS <= sop_pos((3+1)*SOP_POS_WIDTH-1 downto 3*SOP_POS_WIDTH);
     TX1_EOP_POS <= eop_pos((3+1)*EOP_POS_WIDTH-1 downto 3*EOP_POS_WIDTH);

end architecture FLU_FORK_1TO4_ARCH;
