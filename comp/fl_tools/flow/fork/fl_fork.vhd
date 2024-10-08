--
-- fl_fork.vhd: Fork component for Frame link
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
entity FL_FORK is
   generic(
       DATA_WIDTH:   integer:=32;
       OUTPUT_PORTS: integer:=2
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

      -- Frame link concentrated interface
      TX_DATA        : out std_logic_vector(OUTPUT_PORTS*DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(OUTPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_EOF_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_SOP_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_EOP_N       : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_SRC_RDY_N   : out std_logic_vector(OUTPUT_PORTS-1 downto 0);
      TX_DST_RDY_N   : in  std_logic_vector(OUTPUT_PORTS-1 downto 0)
     );
end entity FL_FORK;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_FORK_ARCH of FL_FORK is
signal DST_RDY: std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal SRC_RDY: std_logic;
begin

  divider: for i in 1 to OUTPUT_PORTS generate
    TX_DATA(i*DATA_WIDTH-1 downto (i-1)*DATA_WIDTH)<=RX_DATA;
    TX_REM(i*log2(DATA_WIDTH/8)-1 downto (i-1)*log2(DATA_WIDTH/8))<=RX_REM;
    TX_SOF_N(i-1)<=RX_SOF_N;
    TX_EOF_N(i-1)<=RX_EOF_N;
    TX_SOP_N(i-1)<=RX_SOP_N;
    TX_EOP_N(i-1)<=RX_EOP_N;
  end generate divider;

  DST_RDY(0)<=TX_DST_RDY_N(0);

  gen: for i in 1 to OUTPUT_PORTS-1 generate
  DST_RDY(i)<=DST_RDY(i-1) or TX_DST_RDY_N(i);
  end generate gen;

  RX_DST_RDY_N<=DST_RDY(OUTPUT_PORTS-1);

  gendst: for i in 0 to OUTPUT_PORTS-1 generate
  process(TX_DST_RDY_N, RX_SRC_RDY_N)
  variable orbit : std_logic := '0';
  variable j: integer ;
  begin
    orbit := '0';
    for j in 0 to OUTPUT_PORTS - 1 loop
        if not (j = i) then
           orbit := orbit or TX_DST_RDY_N(j);
        end if;
    end loop;
    TX_SRC_RDY_N(i) <= orbit or RX_SRC_RDY_N;
  end process;
  end generate;

end architecture FL_FORK_ARCH;
