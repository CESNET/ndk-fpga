-- count48_top.vhd
--!
--! \file
--! \brief COUNTER  implemented with Virtex-7 DSP slice
--! Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

--! \brief DSP slice ALU entity
entity COUNT_TOP is
   generic (
      DATA_WIDTH  : integer := 96;
      --! Input pipeline registers (0, 1)
      REG_IN      : integer := 0;
      --
      AUTO_RESET  : integer := 1
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Enable input
      ENABLE   : in std_logic;
      --! Reset input
      RESET    : in  std_logic;
      --! Data input
      A        : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
      --! max value
      MAX      : in  std_logic_vector((DATA_WIDTH - 1) downto 0);
      --! Data output
      P        : out std_logic_vector((DATA_WIDTH - 1) downto 0)
     );
end COUNT_TOP;

--! Vitrex-7 architecture of COUNT48
architecture V7_DSP_TOP of COUNT_TOP is

   --! signals
   signal reset_D     : std_logic;
   signal a_D         : std_logic_vector((DATA_WIDTH - 1) downto 0);
   signal max_D       : std_logic_vector((DATA_WIDTH - 1) downto 0);
   signal enable_p    : std_logic;
   signal p_D         : std_logic_vector((DATA_WIDTH - 1) downto 0);

begin

 uut : entity work.COUNT_DSP(structural)
    generic map (
      DATA_WIDTH => DATA_WIDTH,
      REG_IN  => REG_IN,
      AUTO_RESET => AUTO_RESET
    )
    port map (
      CLK         => CLK,
      RESET       => reset_D,
      A           => a_D,
      MAX         => max_D,
      ENABLE      => enable_p,
      P           => p_D
   );

    -- input registers
   process(CLK)
	begin
	   if (CLK'event) and (CLK='1') then
 	    if (RESET='1') then
	      reset_D <= '1';
   	      a_D <= (others => '0');
              enable_p <= '0';
              max_D <= (others => '0');
            else
              reset_D <= '0';
  	      a_D <= A;
              enable_p <= ENABLE;
              max_D <= MAX;
            end if;
  	  end if;
 	end process;

   -- output registers
   process(CLK)
	begin
	  if (CLK'event) and (CLK='1') then
 	    if (RESET='1') then
              P <=(others => '0');
	    else
              P <= p_D;
  	    end if;
  	  end if;
 	end process;

end V7_DSP_TOP;
