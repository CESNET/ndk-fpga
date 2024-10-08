--! testbench.vhd: Testbench for DP_URAM_XILINX
--! # Copyright (C) 2015 CESNET
--! # Author: Kamil Vojanec <xvojan00@stud.fit.vutbr.cz>
--
--! SPDX-License-Identifier: BSD-3-Clause
--
--! $Id$
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper            : time := 10 ns; -- Clock period
   constant reset_time        : time := 2*clkper + 5 ns; -- Reset duration
   constant DATA_WIDTH        : integer := 37;
   constant ADDRESS_WIDTH     : integer := 12;
   constant EXTERNAL_OUT_REG    : boolean := false;
   constant DEVICE            : string := "ULTRASCALE";
   constant ADDITIONAL_REG      : integer := 0;
   constant INTERNAL_OUT_REG      : boolean := false;
   constant DEBUG_ASSERT_UNINITIALIZED : boolean := true;
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

   --! BRAM_XILINX
   uut : entity work.DP_URAM_XILINX
   generic map (
      --! Input data width
      DATA_WIDTH     => DATA_WIDTH,
      --! Address bus width
      ADDRESS_WIDTH  => ADDRESS_WIDTH,
      --! Enable output register
      EXTERNAL_OUT_REG => EXTERNAL_OUT_REG,
      --! Set input -> output latency
      ADDITIONAL_REG   => ADDITIONAL_REG,
      --! Select target device "VIRTEX5", "VIRTEX6", "7SERIES", "SPARTAN6"
      DEVICE         => DEVICE,
      INTERNAL_OUT_REG   => INTERNAL_OUT_REG,
      DEBUG_ASSERT_UNINITIALIZED => DEBUG_ASSERT_UNINITIALIZED
   )
   port map (
       --! \name Interface A
      --! Clock A
      CLK   => CLK,
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

      --! \name Interface B,
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
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- write on B, address -> 0
      DIB    <= (35 =>'1', others => '0');
      WEB    <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      WEB    <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');

      -- read from A, address 0
      REA   <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      REA   <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');
      --Write to B, address 42, read from A, address 41, 42, 43
      ADDRA <= std_logic_vector(to_unsigned(42, ADDRESS_WIDTH));
      DIA   <= std_logic_vector(to_unsigned(18, DATA_WIDTH));
      WEA   <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');

      WEA   <= '0';
      wait for 5*clkper; wait until (CLK'event and CLK = '1');
      REB   <= '1';
      REA   <= '1';
      ADDRA <= std_logic_vector(to_unsigned(40, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(42, ADDRESS_WIDTH));
      wait for clkper; wait until (CLK'event and CLK ='1');
      REA   <= '0';
      REB   <= '0';
      --! Port A write, port B read. Same address
      wait for 2*clkper; wait until (CLK'event and CLK = '1');
      REA <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      REA <= '0';
      wait for 10*clkper; wait until (CLK'event and CLK = '1');
      ADDRA <= std_logic_vector(to_unsigned(88, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(88, ADDRESS_WIDTH));
      DIA <= std_logic_vector(to_unsigned(36, DATA_WIDTH));
      WEA <= '1';
      REB <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      WEA <= '0';
      REB <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');
      --! Port B write, port A read. Same address
      ADDRA <= std_logic_vector(to_unsigned(66, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(66, ADDRESS_WIDTH));
      DIB <= std_logic_vector(to_unsigned(120, DATA_WIDTH));
      REA <= '1';
      WEB <= '1';
      wait for clkper; wait until (CLK'event and CLK = '1');
      REA <= '0';
      WEB <= '0';
      wait for clkper; wait until (CLK'event and CLK = '1');
      WEA <= '1';
      REB <= '1';
      ADDRA <= std_logic_vector(to_unsigned(90, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(90, ADDRESS_WIDTH));
      DIA <= std_logic_vector(to_unsigned(36, DATA_WIDTH));
      wait for clkper; wait until (CLK'event and CLK = '1');
      ADDRA <= std_logic_vector(to_unsigned(91, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(91, ADDRESS_WIDTH));
      DIA <= std_logic_vector(to_unsigned(39, DATA_WIDTH));
      wait for clkper; wait until (CLK'event and CLK = '1');
      ADDRA <= std_logic_vector(to_unsigned(92, ADDRESS_WIDTH));
      ADDRB <= std_logic_vector(to_unsigned(92, ADDRESS_WIDTH));
      DIA <= std_logic_vector(to_unsigned(38, DATA_WIDTH));
      wait for clkper; wait until (CLK'event and CLK = '1');
      WEA <= '0';
      REB <= '0';
      PIPE_ENA <= '0';
      PIPE_ENB <= '0';
      wait for 4*clkper; wait until (CLK'event and CLK = '1');
      PIPE_ENA <= '1';
      PIPE_ENB <= '1';
      wait;
   end process input_flow;
end architecture;
