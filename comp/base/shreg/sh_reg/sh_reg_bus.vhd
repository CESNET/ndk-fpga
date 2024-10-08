--
-- sh_reg_bus.vhd: Shift Register Bus
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas <martinek@liberouter.org>
--            Radek Iša      <xisara00@stud.fit.vutbr.cz>
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
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sh_reg_bus is
   generic(
      NUM_BITS    : integer := 16;
      -- INIT        : std_logic_vector(15 downto 0) := X"0000";
      -- INIT_EXT00  : std_logic_vector(63 downto 0) := X"0000000000000000";
      INIT        : std_logic_vector := x"0000";
      INIT_EXT00  : std_logic_vector := X"0000000000000000";
      DATA_WIDTH  : integer := 1
   );
   port(
      CLK      : in  std_logic;

      DIN      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      CE       : in  std_logic;
      DOUT     : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity sh_reg_bus;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_reg_bus is

begin


 SH_REG_BUS : entity work.SH_REG_BASE_STATIC
   generic map(
     DATA_WIDTH => DATA_WIDTH,
     NUM_BITS   => NUM_BITS,
     INIT_TYPE  => 1,
     INIT       => INIT & INIT_EXT00,
     IS_CLK_INVERTED => '0'
   )
   port map(
     CLK => CLK,
     CE  => CE,

     DIN  => DIN,
     DOUT => DOUT
   );

end architecture behavioral;

