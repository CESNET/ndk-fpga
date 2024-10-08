-- shifter_one.vhd: Left or right bit-by-bit shifter or rotator
-- Copyright (C) 2017 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.numeric_std.all;
use WORK.math_pack.all;



entity shifter_one is
  generic(
    DATA_WIDTH : integer := 64;
    MOVE_LEFT : boolean := true; -- moving left when true, right when false
    ROTATE : boolean := false -- rotating when true, shifting when false
  );
  port(
    DI      : in std_logic_vector(DATA_WIDTH-1 downto 0);
    SEL     : in std_logic_vector(max(1,log2(DATA_WIDTH))-1 downto 0);
    DO      : out std_logic_vector(DATA_WIDTH-1 downto 0)
  );
end entity;



architecture behavioral of shifter_one is

begin

  empty_gen: if DATA_WIDTH = 1 generate
    DO <= DI;
  end generate;

  full_shift_left_gen: if DATA_WIDTH > 1 and MOVE_LEFT and not ROTATE generate
    DO <= DI sll conv_integer(SEL);
  end generate;

  full_shift_right_gen: if DATA_WIDTH > 1 and not MOVE_LEFT and not ROTATE generate
    DO <= DI srl conv_integer(SEL);
  end generate;

  full_rotate_left_gen: if DATA_WIDTH > 1 and MOVE_LEFT and ROTATE generate
    DO <= DI rol conv_integer(SEL);
  end generate;

  full_rotate_right_gen: if DATA_WIDTH > 1 and not MOVE_LEFT and ROTATE generate
    DO <= DI ror conv_integer(SEL);
  end generate;

end architecture;
