-- shifter.vhd: Left or right block-by-block shifter
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



entity shifter is
  generic(
    BLOCKS : integer := 64;
    BLOCK_WIDTH : integer := 1;
    MOVE_LEFT : boolean := true; -- moving left when true, right when false
    ROTATE : boolean := false -- rotating when true, shifting when false
  );
  port(
    DI      : in std_logic_vector(BLOCKS*BLOCK_WIDTH-1 downto 0);
    SEL     : in std_logic_vector(max(1,log2(BLOCKS))-1 downto 0);
    DO      : out std_logic_vector(BLOCKS*BLOCK_WIDTH-1 downto 0)
  );
end entity;



architecture arch of shifter is
  type shift_array_t is array(0 to BLOCK_WIDTH-1) of std_logic_vector(BLOCKS-1 downto 0);
  signal di_sa, do_sa : shift_array_t;
begin

  empty_gen: if BLOCKS = 1 generate
    DO <= DI;
  end generate;


  full_gen: if BLOCKS > 1 generate

    onebit_shifters_gen: for i in 0 to BLOCK_WIDTH-1 generate

      data_realign_gen: for j in 0 to BLOCKS-1 generate
        di_sa(i)(j) <= DI(j*BLOCK_WIDTH+i);
        DO(j*BLOCK_WIDTH+i) <= do_sa(i)(j);
      end generate;

      onebit_shifter: entity work.shifter_one
      generic map (
        DATA_WIDTH => BLOCKS,
        MOVE_LEFT  => MOVE_LEFT,
        ROTATE     => ROTATE
      ) port map (
        DI  => di_sa(i),
        SEL => SEL,
        DO  => do_sa(i)
      );

    end generate;

  end generate;

end architecture;
