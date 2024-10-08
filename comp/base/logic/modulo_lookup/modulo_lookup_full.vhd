--!
--! \file modulo_lookup_full.vhd
--! \brief Implementation of Modulo look-up table
--! \author Jan Kučera <xkuce73@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

--! Package with log2 function.
use work.math_pack.all;

--! \brief Implementation of Modulo look-up table
architecture behavioral of MODULO_LOOKUP is

   -- Type & constant declaration ---------------------------------------------

   attribute ram_style : string;
   constant ITEMS : integer := 2**(OPERAND_WIDTH+MODULO_WIDTH);
   constant ADDR_WIDTH : integer := OPERAND_WIDTH+MODULO_WIDTH;
   type t_mem is array(0 to ITEMS-1) of std_logic_vector(MODULO_WIDTH-1 downto 0);


   -- Memory initialization function ------------------------------------------

   function INIT_MEM return t_mem is
      variable init : t_mem;
      variable addr : std_logic_vector(ADDR_WIDTH-1 downto 0);
   begin
      for i in 1 to 2**MODULO_WIDTH loop
         for j in 0 to 2**OPERAND_WIDTH-1 loop
            init(j*2**MODULO_WIDTH+i-1) := conv_std_logic_vector(j mod i, MODULO_WIDTH);
         end loop;
      end loop;

      return init;
   end function;


   -- Signal declaration ------------------------------------------------------

   signal addr     : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal data     : std_logic_vector(MODULO_WIDTH-1 downto 0);

   signal reg_data : std_logic_vector(MODULO_WIDTH-1 downto 0);
   signal reg_vld1 : std_logic;
   signal reg_vld2 : std_logic;

   signal memory : t_mem := INIT_MEM;
   attribute ram_style of memory: signal is MEM_TYPE;


begin

   addr <= OPERAND & MODULO;

   rom_p: process(CLK)
   begin
      if (CLK'event and CLK = '1') then
         data <= memory(conv_integer(unsigned(addr)));
      end if;
   end process;

   output_reg_gen: if (OUTPUT_REG = true) generate
      output_reg_p: process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            if (RESET = '1') then
               reg_data <= (others => '0');
               reg_vld1 <= '0';
               reg_vld2 <= '0';
            else
               reg_data <= data;
               reg_vld1 <= IN_VLD;
               reg_vld2 <= reg_vld1;
            end if;
         end if;
      end process;

      RESULT <= reg_data;
      OUT_VLD <= reg_vld2;
   end generate;

   nooutput_reg_gen: if (OUTPUT_REG = false) generate
      nooutput_reg_p: process(RESET, CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if (RESET = '1') then
               OUT_VLD <= '0';
            else
               OUT_VLD <= IN_VLD;
            end if;
         end if;
      end process;

      RESULT <= data;
   end generate;

end architecture;
