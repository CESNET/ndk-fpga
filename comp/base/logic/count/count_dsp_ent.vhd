-- count_dsp_ent.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity COUNT_DSP is
   generic (
      DATA_WIDTH   : integer := 48;
      --! Input pipeline registers
      REG_IN       : integer := 0;
      --! Reset when MAX == P ( 0 => "NO_RESET", 1 => "RESET_MATCH")
      AUTO_RESET   : integer := 0;
      --! Use DSP slices
      DSP_EN       : boolean := true;
      --! true -> UP or false -> DOWN, only when DSP_EN = false
      DIR          : boolean := true;

      DEVICE       : string := "7SERIES"
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Enable input
      ENABLE   : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data input (must MAX % A = 0), Maximum value
      MAX      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      --! Data output
      P        : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity;
