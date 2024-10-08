-- data_shifter.vhd
-- Copyright (C) 2012 CESNET
-- Author: Lukas Kekely <kekely@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id:$
--
-- TODO:
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Entity declaration: DATA_SHIFTER
-- ----------------------------------------------------------------------------
entity DATA_SHIFTER is
   generic
   (
      DATA_WIDTH      : integer := 256;
      SOP_POS_WIDTH   : integer := 2
   );
   port(
      -- common signals
      CLK           : in  std_logic;
      RESET         : in  std_logic;

      DATA_IN       : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DATA_IN_VLD   : in  std_logic;
      DATA_OUT      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DATA_OUT_VLD  : out std_logic;
      SEL           : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0)
   );
end entity DATA_SHIFTER;


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--  Architecture: DATA_SHIFTER
-- ----------------------------------------------------------------------------
architecture arch of DATA_SHIFTER is
   constant BLOCKS     : integer := 2**SOP_POS_WIDTH;
   constant BLOCK_SIZE : integer := DATA_WIDTH/BLOCKS;

   type blocks_t is array (BLOCKS-1 downto 0) of std_logic_vector(BLOCK_SIZE-1 downto 0);
   type blocks2_t is array (2*BLOCKS-1 downto 0) of std_logic_vector(BLOCK_SIZE-1 downto 0);
   type bmatrix_t is array (BLOCKS-1 downto 0) of blocks2_t;
   signal input      : blocks_t;
   signal output     : blocks_t;
   signal reg        : blocks_t;
   signal shifted    : blocks2_t;
   signal shift_pos  : bmatrix_t;

begin
   IO_map_gen : for i in 0 to BLOCKS-1 generate
      input(i) <= DATA_IN((i+1)*BLOCK_SIZE-1 downto i*BLOCK_SIZE);
      DATA_OUT((i+1)*BLOCK_SIZE-1 downto i*BLOCK_SIZE) <= output(i);
   end generate;
   DATA_OUT_VLD <= DATA_IN_VLD;

   shift_possibilities_gen : for i in 0 to BLOCKS-1 generate
      shift_possibility_gen : for j in 0 to BLOCKS-1 generate
         shift_pos(i)(i+j) <= input(j);
      end generate;
   end generate;
   shifted <= shift_pos(conv_integer(SEL));


   registers_gen : for i in 0 to BLOCKS-2 generate
      process(CLK)
      begin
         if CLK'event and CLK='1' then
            if RESET='1' then
               reg(i) <= (others => '0');
            elsif DATA_IN_VLD='1' then
               reg(i) <= shifted(i+BLOCKS);
            end if;
         end if;
      end process;
   end generate;


   muxes_gen : for i in 0 to BLOCKS-2 generate
      output(i) <= shifted(i) when SEL<=conv_std_logic_vector(i,SOP_POS_WIDTH) else reg(i);
   end generate;
   output(BLOCKS-1) <= shifted(BLOCKS-1);

end architecture;

