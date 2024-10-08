
--
-- testbench.vhd: Testbench for SP_URAM_XILINX
-- Copyright (C) 2018 CESNET
-- Author(s): Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
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
architecture SP_URAM_XILINX of testbench is
   signal CLK : std_logic := '1';
   signal RST : std_logic := '0';
   signal PIPE_EN : std_logic := '1';
   signal REG_CE : std_logic := '1';
   signal RE : std_logic := '0';
   signal WE : std_logic := '0';
   signal ADDR : std_logic_vector(11 downto 0);
   signal DI : std_logic_vector(71 downto 0);
   signal DO : std_logic_vector(71 downto 0);
   signal DO_DV : std_logic;
begin
   uut: entity work.SP_URAM_XILINX
   generic map(
      DEVICE                  => "ULTRASCALE",
      DATA_WIDTH              => 72,
      ADDRESS_WIDTH           => 12,
      WRITE_MODE              => "READ_FIRST",
      ADDITIONAL_REG            => 0,
      EXTERNAL_OUT_REG        => false,
      INTERNAL_OUT_REG            => false
   )
   port map(
      CLK         => CLK,
      RST         => RST,
      PIPE_EN     => PIPE_EN,
      RE          => RE,
      WE          => WE,
      ADDR        => ADDR,
      DI          => DI,
      DO          => DO,
      DO_DV       => DO_DV
   );

   CLK <= not CLK after 10 ns;

   test : process
   begin
   RST <= '1';
   wait for 80 ns;
   RST <= '0';
   PIPE_EN <= '1';
   wait for 80 ns;
   ADDR <= std_logic_vector(to_unsigned(48,12));
   DI <= std_logic_vector(to_unsigned(121, 72));
   WE <= '1';
   RE <= '1';
   wait for 20 ns;
   WE <= '0';
   RE <= '0';
   wait for 20 ns;

   ADDR <= std_logic_vector(to_unsigned(42, 12));
   DI <= std_logic_vector(to_unsigned(22,72));
   WE <= '1';
   wait for 20 ns;
   WE <= '0';
   RE <= '1';
   wait for 20 ns;
   RE <= '0';
   wait for 20 ns;
   RE <= '1';
   wait for 20 ns;
   RE <= '0';
   wait for 20 ns;
   ADDR <= std_logic_vector(to_unsigned(99, 12));
   DI <= std_logic_vector(to_unsigned(44, 72));
   WE <= '1';
   wait for 20 ns;
   WE <= '0';
   RE <= '1';
   wait for 20 ns;
   RE <= '0';
   wait for 60 ns;
   ADDR <= std_logic_vector(to_unsigned(77, 12));
   DI <= std_logic_vector(to_unsigned(66, 72));
   WE <= '1';
   wait for 20 ns;
   WE <= '0';
   RE <= '1';
   wait for 20 ns;
   RE <= '0';
   wait for 40 ns;
   ADDR <= std_logic_vector(to_unsigned(48,12));
   DI <= std_logic_vector(to_unsigned(111, 72));
   WE <= '1';
   RE <= '1';
   wait for 20 ns;
   ADDR <= std_logic_vector(to_unsigned(49,12));
   DI <= std_logic_vector(to_unsigned(121, 72));
   wait for 20 ns;
   ADDR <= std_logic_vector(to_unsigned(50,12));
   DI <= std_logic_vector(to_unsigned(131, 72));
   wait for 20 ns;
   ADDR <= std_logic_vector(to_unsigned(51,12));
   DI <= std_logic_vector(to_unsigned(231, 72));
   wait for 20 ns;
   PIPE_EN <= '0';
   WE <= '0';
   RE <= '0';
   wait for 20 ns;
   ADDR <= std_logic_vector(to_unsigned(54,12));
   DI <= std_logic_vector(to_unsigned(261, 72));
   WE <= '1';
   RE <= '1';
   wait for 20 ns;
   WE <= '0';
   RE <= '0';
   wait for 60 ns;
   PIPE_EN <= '1';
   wait;
   end process;


end architecture SP_URAM_XILINX;

