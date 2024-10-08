-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity INIT_STATS is
   generic(
      ADDRESS_WIDTH  : integer := 10;
      CNT_WIDTH      : integer := 10
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      IN_ADDR        : in  std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      IN_RM          : in  std_logic;
      IN_RM_ALL      : in  std_logic;
      IN_NEXT        : out std_logic;

      OUT_ADDR       : out std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      OUT_RM         : out std_logic;
      OUT_RM_ALL     : out std_logic;
      OUT_NEXT       : in std_logic
   );
end entity;

architecture FULL of INIT_STATS is
   signal pipe_reset : std_logic;
   signal sel        : std_logic;
begin

   process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         pipe_reset <= RESET;
      end if;
   end process;

   sel <= '1' when pipe_reset = '1' and RESET = '0' else
          '0';

   OUT_ADDR    <= IN_ADDR;
   OUT_RM      <= IN_RM when sel = '0' else
                  '1';
   OUT_RM_ALL  <= IN_RM_ALL when sel = '0' else
                  '1';
   IN_NEXT     <= OUT_NEXT;

end architecture;
