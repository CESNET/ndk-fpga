--! testbench.vhd: Testbench for BRAM_XILINX
--! # Copyright (C) 2015 CESNET
--! # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper            : time := 10 ns; -- Clock period
   constant reset_time        : time := 2*clkper + 5 ns; -- Reset duration
   constant DATA_WIDTH        : integer := 37;
   constant ADDRESS_WIDTH     : integer := 12;
   constant BRAM_TYPE         : integer := 36;
   constant ENABLE_OUT_REG    : boolean := true;
   constant DEVICE            : string := "ULTRASCALE";

   --! Clock and reset signals
   signal CLK       : std_logic;
   signal RESET     : std_logic;
   signal PIPE_EN   : std_logic;
   signal RE        : std_logic;
   signal WE        : std_logic;
   signal ADDR      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal DI        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal DO_DV     : std_logic;
   signal DO        : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

   --! BRAM_XILINX
   uut : entity work.SP_BRAM_XILINX
   generic map (
      --! Input data width
      DATA_WIDTH     => DATA_WIDTH,
      --! Address bus width
      ADDRESS_WIDTH  => ADDRESS_WIDTH,
      --! Block Ram Type, only 18Kb,36Kb blocks
      BRAM_TYPE      => BRAM_TYPE,
      --! Enable output register
      ENABLE_OUT_REG => ENABLE_OUT_REG,
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      DEVICE         => DEVICE
   )
   port map (
       --! \name Interface A
      --! Clock A
      CLK   => CLK,
      --! CLKA sync reset
      RST   => RESET,
      --! Pipe enable
      PIPE_EN => PIPE_EN,
      --! Read Enable
      RE    => RE,
      --! Write enable
      WE    => WE,
      --! Address A
      ADDR  => ADDR,
      --! Data A In
      DI    => DI,
      --! Data A Valid
      DO_DV => DO_DV,
      --! Data A Out
      DO    => DO
   );

   --Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   --Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   --! Simulating input flow
   input_flow : process
   begin
      PIPE_EN <= '1';
      RE    <= '0';
      WE    <= '0';
      ADDR  <= (others => '0');
      DI    <= (others => '0');

      wait for reset_time;
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- write on A, address -> 0
      DI    <= (35 =>'1', others => '0');
      WE    <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      WE    <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- read on A, address -> 0
      RE    <= '1';
      ADDR  <= (0 => '0', others => '0');
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- read on B, address -> 1
      RE    <= '1';
      ADDR  <= (0 => '1', others => '0');
      wait for clkper; wait until (CLK'event and CLK = '1');
      RE    <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- write on A, address -> X'802
      DI    <= (36 =>'1', others => '0');
      ADDR  <= (11 => '1', 1 => '1', others => '0');
      WE    <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- read on A, address -> X'802
      WE    <= '0';
      RE    <= '1';
      ADDR  <= (11 => '1', 1 => '1', others => '0');
      wait for clkper; wait until (CLK'event and CLK = '1');
      RE    <= '0';
      wait;
   end process input_flow;
end architecture;
