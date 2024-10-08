-- to2n.vhd: convert numbers to format 2^N
-- Copyright (C) 2015 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- convert binary to 2^N
entity TO2N is
   generic (
      MAX_NUM : integer := 64
   );
   port (
      DATA_IN : in std_logic_vector(log2(MAX_NUM) - 1 downto 0);
      DATA_OUT : out std_logic_vector(MAX_NUM - 1 downto 0)
   );
end TO2N;

architecture full of TO2N is
   signal tmp : std_logic_vector(MAX_NUM downto 0);
begin
      GEN_OUT: for I in 1 to MAX_NUM generate
         DATA_OUT(I-1) <= '1' when DATA_IN = I
                              else '0';
      end generate;
end architecture;
