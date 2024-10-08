
--
-- testbench.vhd:
-- Copyright (C) 2004 CESNET
-- Author(s): Pecenka Tomas <pecenka@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture SDP_URAM_XILINX of testbench is
   signal CLK : std_logic := '1';
   signal RSTB : std_logic := '0';
   signal PIPE_EN : std_logic := '1';
   signal REB : std_logic := '0';
   signal WEA : std_logic := '0';
   signal ADDRA : std_logic_vector(11 downto 0);
   signal ADDRB : std_logic_vector(11 downto 0);
   signal DIA : std_logic_vector(71 downto 0);
   signal DOB : std_logic_vector(71 downto 0);
   signal DOB_DV : std_logic;
begin
   uut: entity work.SDP_URAM_XILINX
   generic map(
      DEVICE                        => "BEHAVIORAL",
      WRITE_MODE                    => "WRITE_FIRST",
      DATA_WIDTH                    => 72,
      ADDRESS_WIDTH                 => 12,
      ADDITIONAL_REG                => 0,
      EXTERNAL_OUT_REG              => false,
      INTERNAL_OUT_REG              => false,
      DEBUG_ASSERT_UNINITIALIZED    => true
   )
   port map(
      CLK            => CLK,
      RSTB           => RSTB,
      PIPE_EN        => PIPE_EN,
      REB            => REB,
      WEA            => WEA,
      ADDRA          => ADDRA,
      ADDRB          => ADDRB,
      DIA            => DIA,
      DOB            => DOB,
      DOB_DV         => DOB_DV
   );

   CLK <= not CLK after 10 ns;

   test : process
   begin
   RSTB <= '1';
   wait for 80 ns;
   RSTB <= '0';
   PIPE_EN <= '1';
   wait for 80 ns;
   ADDRA <= std_logic_vector(to_unsigned(48,12));
   ADDRB <= std_logic_vector(to_unsigned(48,12));
   DIA <= std_logic_vector(to_unsigned(121, 72));
   WEA <= '1';
   REB <= '1';
   wait for 20 ns;
   WEA <= '0';
   REB <= '0';
   wait for 20 ns;

   ADDRA <= std_logic_vector(to_unsigned(42, 12));
   DIA <= std_logic_vector(to_unsigned(22,72));
   WEA <= '1';
   wait for 20 ns;
   ADDRB <= std_logic_vector(to_unsigned(42, 12));
   WEA <= '0';
   REB <= '1';
   wait for 20 ns;
   REB <= '0';
   wait for 20 ns;
   REB <= '1';
   wait for 20 ns;
   REB <= '0';
   wait for 20 ns;
   ADDRA <= std_logic_vector(to_unsigned(99, 12));
   DIA <= std_logic_vector(to_unsigned(44, 72));
   WEA <= '1';
   wait for 20 ns;
   ADDRB <= std_logic_vector(to_unsigned(99, 12));
   WEA <= '0';
   REB <= '1';
   wait for 20 ns;
   REB <= '0';
   wait for 60 ns;
   ADDRA <= std_logic_vector(to_unsigned(77, 12));
   DIA <= std_logic_vector(to_unsigned(66, 72));
   WEA <= '1';
   wait for 20 ns;
   ADDRB <= std_logic_vector(to_unsigned(77, 12));
   WEA <= '0';
   REB <= '1';
   wait for 20 ns;
   REB <= '0';
   wait for 40 ns;
   ADDRA <= std_logic_vector(to_unsigned(48,12));
   ADDRB <= std_logic_vector(to_unsigned(48,12));
   DIA <= std_logic_vector(to_unsigned(111, 72));
   WEA <= '1';
   REB <= '1';
   wait for 20 ns;
   ADDRA <= std_logic_vector(to_unsigned(49,12));
   ADDRB <= std_logic_vector(to_unsigned(49,12));
   DIA <= std_logic_vector(to_unsigned(121, 72));
   wait for 20 ns;
   ADDRA <= std_logic_vector(to_unsigned(50,12));
   DIA <= std_logic_vector(to_unsigned(131, 72));
   wait for 20 ns;
   ADDRA <= std_logic_vector(to_unsigned(51,12));
   ADDRB <= std_logic_vector(to_unsigned(51,12));
   DIA <= std_logic_vector(to_unsigned(231, 72));
   wait for 20 ns;
   PIPE_EN <= '0';
   WEA <= '0';
   REB <= '0';
   wait for 60 ns;
   PIPE_EN <= '1';
   wait;
   end process;


end architecture SDP_URAM_XILINX;
