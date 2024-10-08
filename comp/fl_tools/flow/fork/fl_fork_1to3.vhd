--
-- fl_fork_1to3.vhd: Three port wrapper for fork component for Frame link
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
entity FL_FORK_1TO3 is
   generic(
       DATA_WIDTH:   integer:=32
   );
   port(
       -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame link input interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_REM         : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOF_N       : in std_logic;
      RX_EOF_N       : in std_logic;
      RX_SOP_N       : in std_logic;
      RX_EOP_N       : in std_logic;
      RX_SRC_RDY_N   : in std_logic;
      RX_DST_RDY_N   : out  std_logic;

      -- Frame link output interfaces
      -- Interface 0
      TX0_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX0_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX0_SOF_N       : out std_logic;
      TX0_EOF_N       : out std_logic;
      TX0_SOP_N       : out std_logic;
      TX0_EOP_N       : out std_logic;
      TX0_SRC_RDY_N   : out std_logic;
      TX0_DST_RDY_N   : in  std_logic;

      -- Interface 1
      TX1_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX1_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX1_SOF_N       : out std_logic;
      TX1_EOF_N       : out std_logic;
      TX1_SOP_N       : out std_logic;
      TX1_EOP_N       : out std_logic;
      TX1_SRC_RDY_N   : out std_logic;
      TX1_DST_RDY_N   : in  std_logic;

      -- Interface 2
      TX2_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX2_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX2_SOF_N       : out std_logic;
      TX2_EOF_N       : out std_logic;
      TX2_SOP_N       : out std_logic;
      TX2_EOP_N       : out std_logic;
      TX2_SRC_RDY_N   : out std_logic;
      TX2_DST_RDY_N   : in  std_logic
     );
end entity FL_FORK_1TO3;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_FORK_1TO3_ARCH of FL_FORK_1TO3 is

-- constants and singnals
constant OUTPUT_PORTS: integer:=3;
signal TX_DATA        : std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
signal TX_REM         : std_logic_vector(OUTPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
signal TX_SOF_N       : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal TX_EOF_N       : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal TX_SOP_N       : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal TX_EOP_N       : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal TX_SRC_RDY_N   : std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal TX_DST_RDY_N   : std_logic_vector(OUTPUT_PORTS-1 downto 0);

begin

-- FL_FORK entity instance
  fl_fork: entity work.FL_FORK
  generic map(
       DATA_WIDTH=>DATA_WIDTH,
       OUTPUT_PORTS=>OUTPUT_PORTS
   )
   port map(
       -- Common interface
      RESET=>RESET,
      CLK=>CLK,

      -- Frame link input interface
      RX_DATA=>RX_DATA,
      RX_REM=>RX_REM,
      RX_SOF_N=>RX_SOF_N,
      RX_EOF_N=>RX_EOF_N,
      RX_SOP_N=>RX_SOP_N,
      RX_EOP_N=>RX_EOP_N,
      RX_SRC_RDY_N=>RX_SRC_RDY_N,
      RX_DST_RDY_N=>RX_DST_RDY_N,

      -- Frame link concentrated interface
      TX_DATA=>TX_DATA,
      TX_REM=>TX_REM,
      TX_SOF_N=>TX_SOF_N,
      TX_EOF_N=>TX_EOF_N,
      TX_SOP_N=>TX_SOP_N,
      TX_EOP_N=>TX_EOP_N,
      TX_SRC_RDY_N=>TX_SRC_RDY_N,
      TX_DST_RDY_N=>TX_DST_RDY_N
     );

-- signal mapping for output port 0
  TX0_DATA<=TX_DATA(DATA_WIDTH-1 downto 0);
  TX0_REM<=TX_REM(log2(DATA_WIDTH/8)-1 downto 0);
  TX0_SOF_N<=TX_SOF_N(0);
  TX0_EOF_N<=TX_EOF_N(0);
  TX0_SOP_N<=TX_SOP_N(0);
  TX0_EOP_N<=TX_EOP_N(0);
  TX0_SRC_RDY_N<=TX_SRC_RDY_N(0);
  TX_DST_RDY_N(0)<=TX0_DST_RDY_N;

-- signal mapping for output port 1
  TX1_DATA<=TX_DATA(2*DATA_WIDTH-1 downto DATA_WIDTH);
  TX1_REM<=TX_REM(2*log2(DATA_WIDTH/8)-1 downto log2(DATA_WIDTH/8));
  TX1_SOF_N<=TX_SOF_N(1);
  TX1_EOF_N<=TX_EOF_N(1);
  TX1_SOP_N<=TX_SOP_N(1);
  TX1_EOP_N<=TX_EOP_N(1);
  TX1_SRC_RDY_N<=TX_SRC_RDY_N(1);
  TX_DST_RDY_N(1)<=TX1_DST_RDY_N;

-- signal mapping for output port 2
  TX2_DATA<=TX_DATA(3*DATA_WIDTH-1 downto 2*DATA_WIDTH);
  TX2_REM<=TX_REM(3*log2(DATA_WIDTH/8)-1 downto 2*log2(DATA_WIDTH/8));
  TX2_SOF_N<=TX_SOF_N(2);
  TX2_EOF_N<=TX_EOF_N(2);
  TX2_SOP_N<=TX_SOP_N(2);
  TX2_EOP_N<=TX_EOP_N(2);
  TX2_SRC_RDY_N<=TX_SRC_RDY_N(2);
  TX_DST_RDY_N(2)<=TX2_DST_RDY_N;

end architecture FL_FORK_1TO3_ARCH;
