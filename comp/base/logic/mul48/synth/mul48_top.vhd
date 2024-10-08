-- mul48_top.vhd
--!
--! \file
--! \brief MUL  implemented with Virtex-7 DSP slice
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
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
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
Library UNISIM;
use UNISIM.vcomponents.all;

--! \brief DSP slice ALU entity
entity MUL48_TOP is
   generic (
      A_DATA_WIDTH : integer := 17;
      B_DATA_WIDTH : integer := 51;
      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 1;
      --! Output pipeline register (0, 1)
      REG_OUT     : integer := 1
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector(A_DATA_WIDTH-1 downto 0);
      --! Data input
      B        : in  std_logic_vector(B_DATA_WIDTH-1 downto 0);
      --! Clock enable for input pipeline registers
      CE_IN    : in  std_logic;
      --! Clock enable for output pipeline registers
      CE_OUT   : in  std_logic;
      --! Data output
      P         : out std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0)
     );
end MUL48_TOP;

--! Vitrex-7 architecture of MUL48
architecture V7_DSP_TOP of MUL48_TOP is

   --! signals
   signal reset_D     : std_logic;
   signal a_D         : std_logic_vector(A_DATA_WIDTH-1 downto 0);
   signal b_D         : std_logic_vector(B_DATA_WIDTH-1 downto 0);
   signal ce_in_D     : std_logic;
   signal ce_out_D    : std_logic;
   signal p_D         : std_logic_vector(A_DATA_WIDTH+B_DATA_WIDTH-1 downto 0);

begin

   uut : entity work.MUL_DSP
   generic map (
      A_DATA_WIDTH => A_DATA_WIDTH,
      B_DATA_WIDTH => B_DATA_WIDTH,
      REG_IN      => REG_IN,
      REG_OUT     => REG_OUT
   )
   port map (
      CLK         => CLK,
      RESET       => reset_D,
      A           => a_D,
      B           => b_D,
      CE_IN       => ce_in_D,
      CE_OUT      => ce_out_D,
      P           => p_D
   );

    -- input registers
   process(CLK)
	begin
	   if (CLK'event) and (CLK='1') then
 	    if (RESET='1') then
              reset_D <= '1';
   	      a_D <= (others => '0');
              b_D <= (others => '0');
              ce_in_D <= '0';
              ce_out_D <= '0';
            else
              reset_D <= '0';
  	      a_D <= A;
              b_D <= B;
              ce_in_D <= CE_IN;
              ce_out_D <= CE_OUT;
   	    end if;
  	  end if;
 	end process;

   -- output registers
   process(CLK)
	begin
	   if (CLK'event) and (CLK='1') then
 	    if (RESET='1') then
              P <= (others => '0');
	    else
              P <= p_D;
  	    end if;
  	  end if;
 	end process;

end V7_DSP_TOP;
