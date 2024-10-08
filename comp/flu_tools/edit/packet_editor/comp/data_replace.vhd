-- data_replace.vhd: entity of packet edit
-- Copyright (C) 2015 CESNET
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

entity DATA_REPLACE is
   generic(
      --! data input/output width
      --! (..., 128, 256, 512, 1024, ...)
      DATA_WIDTH 	   : integer := 512;
      --! enbale output pipe
      PIPE_EN        : boolean := true;
      --! use DSP slice (pipe)
      DSP_ON         : boolean := false
   );
   port(
      CLK         : in std_logic;
      RESET       : in std_logic;
      -- output pipe enable signal
      EN_PIPE     : in std_logic;
      SHIFT       : in std_logic;
      -- new data
      NEW_DATA    : in std_logic_vector((8*4) - 1 downto 0);
      MASK        : in std_logic_vector(3 downto 0);
      --! shift block
      OFFSET      : in std_logic_vector(log2((512/8)/4)-1 downto 0);
      OFFSET_VLD  : in std_logic;
      --! input data
      DATA_IN     : in std_logic_vector(DATA_WIDTH - 1 downto 0);
      DATA_IN_VLD : in std_logic;
      --! output data
      DATA_OUT    : out std_logic_vector(DATA_WIDTH - 1 downto 0);
      FLU_STATE   : in std_logic_vector(2 downto 0)
);
end entity;

architecture full of DATA_REPLACE is
   constant num_bytes         : integer := DATA_WIDTH/8;
   signal offset_conv         : std_logic_vector(num_bytes-1 downto 0);
   signal offset_conv_shift   : std_logic_vector(num_bytes-1 downto 0);

   signal pipe_new_data       : std_logic_vector(15 downto 0);
   signal pipe_first_bytes    : std_logic_vector(1 downto 0);
begin

   process(ALL)
      variable index : integer;
   begin
      index := conv_integer(OFFSET & "00");
      offset_conv <= (others => '0');

      if(OFFSET_VLD = '1') then
         offset_conv(index)   <= MASK(0);
         offset_conv(index+1) <= MASK(1);
         offset_conv(index+2) <= MASK(2);
         offset_conv(index+3) <= MASK(3);
      end if;
   end process;

   process(ALL)
   begin
      offset_conv_shift <= (others => '0');
      offset_conv_shift(1 downto 0) <= pipe_first_bytes;

      if(SHIFT = '1') then
         offset_conv_shift(offset_conv_shift'length-1 downto 2) <= offset_conv(offset_conv'length-1-2 downto 0);
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            pipe_first_bytes <= (others => '0');
         elsif(DATA_IN_VLD = '1') then
            if(SHIFT = '1') then
               pipe_first_bytes <= offset_conv(offset_conv'length-1 downto offset_conv'length-1-1);
            else
               pipe_first_bytes <= (others => '0');
            end if;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if(DATA_IN_VLD = '1') then
            pipe_new_data <= NEW_DATA(8*4-1 downto 8*2);
         end if;
      end if;
   end process;

   GEN_MUXs: for I in 0 to num_bytes - 1 generate
      constant new_index       : integer := I mod 4;
      constant new_shift_index : integer := (I+2) mod 4;

      signal mux_new_data        : std_logic_vector(7 downto 0);
      signal mux_new_data_shift  : std_logic_vector(7 downto 0);
   begin

      mux_new_data <= NEW_DATA((new_index+1)*8-1 downto new_index*8);

      gen_fisrst : if(I < 2) generate
         mux_new_data_shift<= pipe_new_data((I+1)*8-1 downto I*8);
      end generate;

      gen_fisrst_no : if(I >= 2) generate
         mux_new_data_shift<= NEW_DATA((new_shift_index+1)*8-1 downto new_shift_index*8);
      end generate;

      process(ALL)
      begin
         DATA_OUT((I+1)*8-1 downto I*8) <= DATA_IN((I+1)*8-1 downto I*8);

         if(offset_conv(I) = '1' and SHIFT = '0') then
            DATA_OUT((I+1)*8-1 downto I*8) <= mux_new_data;
         end if;

         if(offset_conv_shift(I) = '1') then
            DATA_OUT((I+1)*8-1 downto I*8) <= mux_new_data_shift;
         end if;
      end process;

   end generate;
end architecture;

