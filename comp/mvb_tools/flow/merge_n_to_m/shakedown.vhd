-- shakedown.vhd: Wrapper of MVB merger N to M
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Merges input MVB of N items to output MVB of M items.
-- There can be at most M items valid on input MVB, otherwise,
-- items might get lost, if you . Can be used as combinational logic with
-- ``OUTPUT_REG`` disabled.
--
-- Working principle of SHAKEDOWN.
--   .. image:: doc/shakedown-vld.svg
--
-- Situation with more valid items then OUTPUTS.
--   .. image:: doc/shakedown-inv.svg
--
-- Situation, where there are more vld items on INPUT interface then OUTPUTS.
-- SHAKEDOWN does not solve this situation and when not solved externally,
-- items may get lost.
entity SHAKEDOWN is
   generic(
      -- Number of inputs (at most OUTPUTS valid!!!)
      INPUTS     : integer := 32;
      -- Number of outputs
      OUTPUTS    : integer := 4;
      -- Data width of each input/output in bits
      DATA_WIDTH : integer := 32;
      -- Output register enable
      OUTPUT_REG : boolean := false
   );
   port(
      CLK   : in  std_logic;
      RESET : in  std_logic;

      -- Input data N item MVB
      DIN          : in  std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
      -- Input data valid
      DIN_VLD      : in  std_logic_vector(INPUTS-1 downto 0);
      -- Input data ready
      DIN_SRC_RDY  : in  std_logic := '1';
      DIN_DST_RDY  : out std_logic;

      -- Output data M item MVB
      DOUT         : out std_logic_vector(OUTPUTS*DATA_WIDTH-1 downto 0);
      -- Output data valid
      DOUT_VLD     : out std_logic_vector(OUTPUTS-1 downto 0);
      -- Output data ready
      DOUT_SRC_RDY : out std_logic;
      DOUT_DST_RDY : in  std_logic := '1'
   );
end SHAKEDOWN;

architecture FULL of SHAKEDOWN is

   signal s_din_arr        : slv_array_t(INPUTS-1 downto 0)(DATA_WIDTH-1 downto 0);
   signal s_merge_din_arr  : slv_array_t(INPUTS-1 downto 0)(DATA_WIDTH+1-1 downto 0);
   signal s_merge_dout     : std_logic_vector(OUTPUTS*(DATA_WIDTH+1)-1 downto 0);
   signal s_merge_dout_arr : slv_array_t(OUTPUTS-1 downto 0)(DATA_WIDTH+1-1 downto 0);
   signal s_dout_arr       : slv_array_t(OUTPUTS-1 downto 0)(DATA_WIDTH-1 downto 0);

begin
   assert (RESET = '1') or (count_ones(DIN_VLD) <= OUTPUTS)
      report "[SHAKEDOWN] There are more items valid on DIN interface than DOUT ITEMS, items might be getting lost!"
      severity error;

   s_din_arr <= slv_array_downto_deser(DIN,INPUTS,DATA_WIDTH);

   merge_din_array_g : for i in 0 to INPUTS-1 generate
      s_merge_din_arr(i)(DATA_WIDTH+1-1 downto 1) <= s_din_arr(i);
      s_merge_din_arr(i)(0) <= DIN_VLD(i);
   end generate;

   merge_n_to_m_i : entity work.MERGE_N_TO_M
   generic map (
      INPUTS     => INPUTS,
      OUTPUTS    => OUTPUTS,
      DATA_WIDTH => DATA_WIDTH+1,
      OUTPUT_REG => OUTPUT_REG
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,

      INPUT_DATA     => slv_array_ser(s_merge_din_arr,INPUTS,DATA_WIDTH+1),
      INPUT_SRC_RDY  => DIN_SRC_RDY,
      INPUT_DST_RDY  => DIN_DST_RDY,

      OUTPUT_DATA    => s_merge_dout,
      OUTPUT_SRC_RDY => DOUT_SRC_RDY,
      OUTPUT_DST_RDY => DOUT_DST_RDY
   );

   s_merge_dout_arr <= slv_array_downto_deser(s_merge_dout,OUTPUTS,DATA_WIDTH+1);

   dout_array_g : for i in 0 to OUTPUTS-1 generate
      s_dout_arr(i) <= s_merge_dout_arr(i)(DATA_WIDTH+1-1 downto 1);
      DOUT_VLD(i) <= s_merge_dout_arr(i)(0);
   end generate;

   DOUT <= slv_array_ser(s_dout_arr,OUTPUTS,DATA_WIDTH);

end architecture;
