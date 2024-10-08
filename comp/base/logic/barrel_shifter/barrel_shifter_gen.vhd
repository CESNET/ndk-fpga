--
-- barrel_shifter_gen.vhd: Barrel shifter with generic data width and generic block size
--                         NOTE: barel_shifter.vhd is shifter with 8bit blocks
--                               barel_bit_rotator.vhd is shifter with 1bit blocks
-- Copyright (C) 2017 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--            Vaclav Hummel <xhumme00@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- Generically adjustable barrel shifter where single bits as well as whole blocks can be shifted.
-- The direction can also be set.
entity BARREL_SHIFTER_GEN is
   generic (
      -- input/output data width in BLOCKs
      BLOCKS      : integer := 256;
      -- size of one block in bits
      BLOCK_SIZE  : integer := 64;
      -- set true to shift left, false to shift right
      SHIFT_LEFT  : boolean := false
   );
   port (
      DATA_IN     : in  std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
      DATA_OUT    : out std_logic_vector(BLOCKS*BLOCK_SIZE-1 downto 0);
      SEL         : in  std_logic_vector(log2(BLOCKS)-1 downto 0)
   );
end BARREL_SHIFTER_GEN;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture barrel_shifter_arch of BARREL_SHIFTER_GEN is
   signal data_in_deser : slv_array_t(0 to BLOCKS-1)(BLOCK_SIZE-1 downto 0);
   signal mux_in : slv_array_2d_t(0 to BLOCKS-1)(0 to BLOCKS-1)(BLOCK_SIZE-1 downto 0);
   signal mux_out : slv_array_t(0 to BLOCKS-1)(BLOCK_SIZE-1 downto 0);
   signal mux_sel : std_logic_vector(max(1,log2(BLOCKS))-1 downto 0);
begin

   data_in_deser <= slv_array_to_deser(DATA_IN, BLOCKS, BLOCK_SIZE);

   mux_leftg: if SHIFT_LEFT = true generate
      mux_leftgg: for i in 0 to BLOCKS-1 generate
         mux_leftggg: for j in 0 to BLOCKS-1 generate
            mux_in(i)(j) <= data_in_deser((i-j) mod BLOCKS);
         end generate;
      end generate;
   end generate;

   mux_rightg: if SHIFT_LEFT = false generate
      mux_rightgg: for i in 0 to BLOCKS-1 generate
         mux_rightggg: for j in 0 to BLOCKS-1 generate
            mux_in(i)(j) <= data_in_deser((j+i) mod BLOCKS);
         end generate;
      end generate;
   end generate;

   zero_sel : if (BLOCKS=1) generate
      mux_sel <= (others => '0');
   end generate;
   nonzero_sel : if (BLOCKS/=1) generate
      mux_sel <= SEL;
   end generate;

   muxg: for i in 0 to BLOCKS-1 generate
      muxi: entity work.GEN_MUX
      generic map(
         DATA_WIDTH => BLOCK_SIZE,
         MUX_WIDTH => BLOCKS
      )
      port map(
         DATA_IN => slv_array_ser(mux_in(i), BLOCKS, BLOCK_SIZE),
         SEL => mux_sel,
         DATA_OUT => mux_out(i)
      );
   end generate;

   DATA_OUT <= slv_array_ser(mux_out, BLOCKS, BLOCK_SIZE);


end barrel_shifter_arch;
