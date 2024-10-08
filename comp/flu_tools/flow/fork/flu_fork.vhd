--
-- flu_fork.vhd: Fork component for Frame Link Unaligned
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
entity FLU_FORK is
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
      TX_DST_RDY    : in std_logic_vector(OUTPUT_PORTS-1 downto 0)
   );
end entity FLU_FORK;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FLU_FORK_ARCH of FLU_FORK is
signal DST_RDY: std_logic_vector(OUTPUT_PORTS-1 downto 0);
signal SRC_RDY: std_logic;
begin

  divider: for i in 1 to OUTPUT_PORTS generate
    TX_DATA(i*DATA_WIDTH-1 downto (i-1)*DATA_WIDTH)<=RX_DATA;
    TX_SOP_POS(i*SOP_POS_WIDTH-1 downto (i-1)*SOP_POS_WIDTH)<=RX_SOP_POS;
    TX_EOP_POS(i*log2(DATA_WIDTH/8)-1 downto (i-1)*log2(DATA_WIDTH/8))<=RX_EOP_POS;
    TX_SOP(i-1)<=RX_SOP;
    TX_EOP(i-1)<=RX_EOP;
  end generate divider;

  DST_RDY(0)<=TX_DST_RDY(0);

  gen: for i in 1 to OUTPUT_PORTS-1 generate
  DST_RDY(i)<=DST_RDY(i-1) and TX_DST_RDY(i);
  end generate gen;

  RX_DST_RDY<=DST_RDY(OUTPUT_PORTS-1);

  gendst: for i in 0 to OUTPUT_PORTS-1 generate
  process(TX_DST_RDY, RX_SRC_RDY)
  variable andbit : std_logic := '1';
  variable j: integer ;
  begin
    andbit := '1';
    for j in 0 to OUTPUT_PORTS - 1 loop
        if not (j = i) then
           andbit := andbit and TX_DST_RDY(j);
        end if;
    end loop;
    TX_SRC_RDY(i) <= andbit and RX_SRC_RDY;
  end process;
  end generate;

end architecture FLU_FORK_ARCH;
