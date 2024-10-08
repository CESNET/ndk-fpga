-- edge_detect.vhd: Rising edge detector
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity EDGE_DETECT is
   port(
      CLK         : in std_logic;
      DI          : in std_logic;
      --* One cycle pulse when rising edge was detected on DI
      EDGE        : out std_logic
   );
end entity EDGE_DETECT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of EDGE_DETECT is

signal reg_di : std_logic;

begin

reg_di_p : process(CLK)
begin
   if CLK'event and CLK = '1' then
      reg_di <= DI;
   end if;
end process;

EDGE <= DI and not reg_di;

end architecture behavioral;

