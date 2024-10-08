--! testbench.vhd: Testbench for BRAM_V7
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

   constant clkper            : time := 10 ns; --Clock period
   constant reset_time        : time := 2*clkper + 1 ns; --Reset durati
   constant DATA_WIDTH        : integer := 37;
   constant ADDRESS_WIDTH     : integer := 12;
   constant BRAM_TYPE         : integer := 36;
   constant WRITE_MODE_A      : string := "WRITE_FIRST";
   constant WRITE_MODE_B      : string := "WRITE_FIRST";
   constant ENABLE_OUT_REG    : boolean := false;
   constant DEVICE            : string := "7SERIES";

   --! Clock and reset signals
   signal CLK        : std_logic;
   signal RESET      : std_logic;
   signal PIPE_ENA   : std_logic;
   signal REA        : std_logic;
   signal WEA        : std_logic;
   signal ADDRA      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal DIA        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal DOA_DV     : std_logic;
   signal DOA        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal PIPE_ENB   : std_logic;
   signal REB        : std_logic;
   signal WEB        : std_logic;
   signal ADDRB      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
   signal DIB        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal DOB_DV     : std_logic;
   signal DOB        : std_logic_vector(DATA_WIDTH-1 downto 0);
begin

   --! BRAM_V7
   uut : entity work.DP_BRAM_V7
   generic map (
      --! Input data width
      DATA_WIDTH     => DATA_WIDTH,
      --! Address bus width
      ADDRESS_WIDTH  => ADDRESS_WIDTH,
      --! Block Ram Type, only 18Kb,36Kb blocks
      BRAM_TYPE      => BRAM_TYPE,
      --! What operation will be performed first when both WE and RE are
      --! active? Only for behavioral simulation purpose.
      --! WRITE_FIRST(default) | READ_FIRST | NO_CHANGE
      WRITE_MODE_A   => WRITE_MODE_A,
      WRITE_MODE_B   => WRITE_MODE_B,
      --! Enable output register
      ENABLE_OUT_REG => ENABLE_OUT_REG,
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      DEVICE         => DEVICE
   )
   port map (
       --! \name Interface A
      --! Clock A
      CLKA   => CLK,
      --! CLKA sync reset
      RSTA   => RESET,
      --! Pipe enable
      PIPE_ENA => PIPE_ENA,
      --! Read Enable
      REA    => REA,
      --! Write enable
      WEA    => WEA,
      --! Address A
      ADDRA  => ADDRA,
      --! Data A In
      DIA    => DIA,
      --! Data A Valid
      DOA_DV => DOA_DV,
      --! Data A Out
      DOA    => DOA,

      --! \name Interface B
      --! Clock B
      CLKB   => CLK,
      --! CLKB sync reset
      RSTB   => RESET,
      --! Pipe enable
      PIPE_ENB => PIPE_ENB,
      --! Read Enable
      REB    => REB,
      --! Write enable
      WEB    => WEB,
      --! Address B
      ADDRB  => ADDRB,
      --! Data B In
      DIB    => DIB,
      --! Data B Valid
      DOB_DV => DOB_DV,
      --! Data B Out
      DOB    => DOB
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
      PIPE_ENA <= '1';
      REA    <= '0';
      WEA    <= '0';
      ADDRA  <= (others => '0');
      DIA    <= (others => '0');
      PIPE_ENB <= '1';
      REB    <= '0';
      WEB    <= '0';
      ADDRB  <= (others => '0');
      DIB    <= (others => '0');

      wait for reset_time;
      wait for clkper;
      -- write on B , address -> 0
      DIB    <= (35 =>'1', others => '0');
      WEB    <= '1';
      wait for clkper;
      WEB    <= '0';
      wait for clkper;

      -- read on A,B , address -> 0
      REA    <= '1';
      ADDRA  <= (0 => '0',others => '0');
      REB    <= '1';
      ADDRB  <= (0 => '0',others => '0');
      wait for clkper;

      -- read on B , address -> 1
      REB    <= '1';
      ADDRB  <= (0 => '1',others => '0');
      wait for clkper;
      REB    <= '0';
      REA    <= '0';
      wait for clkper;

      -- write on A , address -> X'802
      DIA    <= (36 =>'1', others => '0');
      ADDRA  <= (11 => '1', 1 => '1', others => '0');
      WEA    <= '1';
      wait for clkper;

      -- read on A,B , address -> X'802
      WEA    <= '0';
      REA    <= '1';
      ADDRA  <= (11 => '1', 1 => '1', others => '0');
      REB    <= '1';
      ADDRB  <= (11 => '1', 1 => '1', others => '0');
      wait for clkper;
      REB    <= '0';
      REA    <= '0';
      wait;
   end process input_flow;
end architecture;
