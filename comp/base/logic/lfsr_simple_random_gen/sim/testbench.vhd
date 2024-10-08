-- testbench.vhd: Testbench
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is

   -- Constants declaration ---------------------------------------------------

   constant CLK_PER    : time := 10 ns;
   constant RESET_TIME : time := 10 * CLK_PER;

   constant DATA_WIDTH : natural := 8;
   constant RESET_SEED : std_logic_vector(DATA_WIDTH-1 downto 0) := std_logic_vector(to_unsigned(1,DATA_WIDTH));

   -- Signals declaration -----------------------------------------------------

   signal clk    : std_logic;
   signal reset  : std_logic;
   signal enable : std_logic;
   signal data   : std_logic_vector(DATA_WIDTH-1 downto 0);

-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   --                              UUT
   -- -------------------------------------------------------------------------

   -- UUT instantiation
   uut: entity work.LFSR_SIMPLE_RANDOM_GEN
   generic map (
      DATA_WIDTH => DATA_WIDTH,
      RESET_SEED => RESET_SEED
   )
   port map(
      CLK    => clk,
      RESET  => reset,
      ENABLE => enable,
      DATA   => data
   );

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating clk
   clk_gen: process
   begin
      clk <= '1';
      wait for CLK_PER / 2;
      clk <= '0';
      wait for CLK_PER / 2;
   end process;

   -- generating reset
   reset_gen: process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process;

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   tb_p : process
   begin
      enable <= '0';
      wait for 20*CLK_PER;
      enable <= '1';
      wait for 44*CLK_PER;
      enable <= '0';
      wait for 9*CLK_PER;
      enable <= '1';
      wait;
   end process;

end architecture behavioral;
