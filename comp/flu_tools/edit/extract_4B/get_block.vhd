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

entity GET_BLOCK is
   generic(
      DATA_WIDTH 	   : integer := 512
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;
      --! shift block
      SEL   : in std_logic_vector(log2((512/8)/4) - 1 downto 0);
      --! input data
      DATA_IN     : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      --! output data
      DATA_OUT    : out std_logic_vector((8*4)-1 downto 0)
   );
end entity;

architecture full of GET_BLOCK is
begin

      -- connect multiplexer
      MUX_inst: entity work.GEN_MUX
      generic map(
         DATA_WIDTH  => 8*4,
         MUX_WIDTH   => (DATA_WIDTH/8)/4
      )
      port map(
         DATA_IN     => DATA_IN,
         SEL         => SEL,
         DATA_OUT    => DATA_OUT
      );

end architecture;

