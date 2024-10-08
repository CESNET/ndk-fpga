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

entity MAC_REPLACE is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      MAC_W          : in  std_logic;
      MAC_DATA       : in  std_logic_vector(6*8-1 downto 0);
      MAC_MASK       : in  std_logic_vector(6-1 downto 0);

      DATA_IN        : in  std_logic_vector(6*8-1 downto 0);
      DATA_OUT       : out std_logic_vector(6*8-1 downto 0)
   );
end entity;

architecture full of MAC_REPLACE is
begin

   gne_muxs : for I in 0 to 5 generate
      signal mux_in1 : std_logic_vector(7 downto 0);
      signal mux_in2 : std_logic_vector(7 downto 0);
      signal mux_out : std_logic_vector(7 downto 0);
   begin

      mux_in1 <= DATA_IN(8*(I+1)-1 downto 8*I);
      mux_in2 <= MAC_DATA(8*(I+1)-1 downto 8*I);

      DATA_OUT(8*(I+1)-1 downto 8*I) <= mux_in2 when MAC_MASK(I) = '1' and MAC_W = '1' else
                                        mux_in1;
   end generate;
end architecture;
