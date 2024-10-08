--!
--! \file testbench.vhd
--! \brief Modulo look-up table testbench
--! \author Jan Kučera <xkuce73@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;

use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--! Package with log2 function
use work.math_pack.all;

--! \brief Testbench Entity declaration
entity testbench is
end entity;

--! \brief Testbench architecture declaration
architecture behavioral of testbench is

   -- Constants declaration ---------------------------------------------------

   constant CLK_PER       : time := 5 ns;
   constant RESET_TIME    : time := 10*CLK_PER+0.5 ns;
   constant MODULO_WIDTH  : integer := 4;
   constant OPERAND_WIDTH : integer := 9;
   constant OUTPUT_REG    : boolean := false;
   constant MEM_TYPE      : string  := "block";


   -- Signals declaration -----------------------------------------------------

   -- Synchronization signals
   signal clk     : std_logic;
   signal reset   : std_logic;
   signal ce      : std_logic_vector(3 downto 0);

   -- Input interface signals
   signal modulo  : std_logic_vector(MODULO_WIDTH-1 downto 0);
   signal operand : std_logic_vector(OPERAND_WIDTH-1 downto 0);
   signal in_vld  : std_logic;

   -- Output interface signals
   signal result  : std_logic_vector(MODULO_WIDTH-1 downto 0);
   signal out_vld : std_logic;


begin

   -- -------------------------------------------------------------------------
   --                          Modulo look-up table
   -- -------------------------------------------------------------------------

   -- Modulo look-up table instantiation
   uut: entity work.MODULO_LOOKUP
   generic map (
      MODULO_WIDTH  => MODULO_WIDTH,
      OPERAND_WIDTH => OPERAND_WIDTH,
      OUTPUT_REG    => OUTPUT_REG,
      MEM_TYPE      => MEM_TYPE
   ) port map (
      -- Common interface
      CLK     => clk,
      RESET   => reset,
      -- Input interface
      MODULO  => modulo,
      OPERAND => operand,
      IN_VLD  => in_vld,
      -- Output interface
      RESULT  => result,
      OUT_VLD => out_vld
   );


   -- -------------------------------------------------------------------------
   --                        Synchronization generators
   -- -------------------------------------------------------------------------

   -- CLK generator process
   clk_gen: process
   begin
      clk <= '1';
      wait for CLK_PER / 2;
      clk <= '0';
      wait for CLK_PER / 2;
   end process clk_gen;

   -- RESET generator process
   reset_gen: process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process reset_gen;


   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   -- Valid bit signal generator
   valid_gen_p: process(clk)
   begin
   	if (clk'event and clk = '1') then
      	if (reset = '1') then
      		in_vld <= '0';
         else
   	      in_vld <= not in_vld;
         end if;
   	end if;
	end process;

   -- Operand signal generator
   operand_gen_p: process(clk)
   begin
   	if (clk'event and clk = '1') then
      	if (reset = '1') then
      		operand <= (others => '0');
         elsif (in_vld = '1') then
   	      operand <= operand + 1;
         end if;
   	end if;
	end process;

   -- Modulo signal generator
   modulo_gen_p: process(clk)
   begin
   	if (clk'event and clk = '1') then
      	if (reset = '1') then
      		modulo <= (others => '0');
         elsif (in_vld = '1' and operand = (OPERAND_WIDTH-1 downto 0 => '1')) then
   	      modulo <= modulo + 1;
         end if;
   	end if;
	end process;

end architecture;
