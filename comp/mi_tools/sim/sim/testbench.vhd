--
-- testbench.vhd: Testbench for MI_Splitter
-- Copyright (C) 2006 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--            Adam Piecek <xpiece00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.conv_std_logic_vector;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use work.all;
use work.mi_sim_pkg.all;
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            ENTITY DECLARATION                             --
-- ----------------------------------------------------------------------------

entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                         ARCHITECTURE DECLARATION                          --
-- ----------------------------------------------------------------------------

architecture behavior of testbench is

   -- Simulation constants ----------------------------------------------------
   constant clk_per      : time    := 10 ns;
   constant reset_time   : time    := 10*clk_per;
   constant C_MAX_DELAY  : integer := 5;

   signal delay_drdy     : integer := 1;
   signal delay_ardy     : integer := 0;

   signal clk : std_logic;
   signal reset : std_logic;

   --  MI interface ---------------------------------------------------
   signal mi32_dwr      : std_logic_vector(31 downto 0);
   signal mi32_addr     : std_logic_vector(31 downto 0);
   signal mi32_be       : std_logic_vector(3 downto 0);
   signal mi32_rd       : std_logic;
   signal mi32_wr       : std_logic;
   signal mi32_ardy     : std_logic;
   signal mi32_drd      : std_logic_vector(31 downto 0); signal mi32_drdy     : std_logic;
   -- Testbench signals
   -- input address to SP_DISTMEM
   signal sig_addr       : std_logic_vector(31 downto 0);
   -- output of register
   signal reg_addr       : std_logic_vector(31 downto 0);
   -- label state of automaton
   signal reg_mux        : std_logic;
   -- clearing shift vector
   signal rm_ardy        : std_logic := '0';
   signal rm_drdy        : std_logic := '0';
   -- read request or write request
   signal rd_or_wr       : std_logic;
   -- shift vectors
   signal shift_ardy   : std_logic_vector(C_MAX_DELAY-1 downto 0) := (others => '0');
   signal shift_drdy   : std_logic_vector(C_MAX_DELAY-1 downto 0) := (others => '0');
   -- vectors of rd_or_wr signals
   signal vector_ardy       : std_logic_vector(C_MAX_DELAY+1-1 downto 0) := (others => '0');
   signal vector_drdy       : std_logic_vector(C_MAX_DELAY+1-1 downto 0) := (others => '0');

begin

   mi_sim_i : entity work.MI_SIM
   generic map (
      MI_SIM_ID => 0
   )
   port map (
      CLK => clk,
      RESET => reset,

      MI32_DWR => mi32_dwr,
      MI32_ADDR => mi32_addr,
      MI32_BE => mi32_be,
      MI32_RD => mi32_rd,
      MI32_WR => mi32_wr,
      MI32_ARDY => mi32_ardy,
      MI32_DRD => mi32_drd,
      MI32_DRDY => mi32_drdy
   );


   mem_i : entity work.SP_DISTMEM
   generic map (
      DATA_WIDTH => 32,
      ITEMS => 64
   )
   port map (
      WCLK => clk,
      WE => mi32_wr,
      ADDR => sig_addr(5 downto 0),
      DI => mi32_dwr,
      DO => mi32_drd
   );

   rd_or_wr <= mi32_rd or mi32_wr;

   -- choose action based of state of automaton
   sig_addr <= mi32_addr when reg_mux = '0' else reg_addr;

   -- delay solution
   mi32_ardy <= vector_ardy(delay_ardy);
   mi32_drdy <= vector_drdy(delay_drdy);

   -- extension by current values of read and write requests
   vector_ardy <= shift_ardy & rd_or_wr;
   vector_drdy <= shift_drdy & rd_or_wr;

   rm_ardy <= '1' when mi32_ardy = '1' else '0';
   rm_drdy <= '1' when mi32_drdy = '1' else '0';

   -- shift processes for synchronization rising edge of ardy and drdy signals
   shift_ardy_p : process(clk)
   begin
      if (clk'event and clk = '1') then
         if (rm_ardy = '1') then
            shift_ardy <= (others => '0');
         else
            shift_ardy <= shift_ardy(shift_ardy'length-2 downto 0) & rd_or_wr;
         end if;
      end if;
   end process;

   shift_drdy_p : process(clk)
   begin
      if (clk'event and clk = '1') then
         if (rm_drdy = '1') then
            shift_drdy <= (others => '0');
         else
            shift_drdy <= shift_drdy(shift_drdy'length-2 downto 0) & mi32_rd;
         end if;
      end if;
   end process;

   -- register for storing address when appear's drdy delay
   reg_p : process(clk)
   begin
      if(clk'event and clk = '1') then
         if (reset = '1') then
            reg_addr <= (others => '0');
         elsif(mi32_ardy = '1') then
            reg_addr <= mi32_addr;
         end if;
      end if;
   end process;

   -- control state automaton for solution of drdy delay
   fsm_p : process(clk)
   begin
      if(clk'event and clk = '1') then
         if (reset = '1') then
            reg_mux <= '0';
         elsif (reg_mux = '0') then
            if (mi32_ardy = '1' and mi32_drdy = '0' and mi32_rd = '1') then
               reg_mux <= '1';
            end if;
         else
            if mi32_ardy = '0' and mi32_drdy = '1' then
               reg_mux <= '0';
            end if;
         end if;
      end if;
   end process;

   clk_gen : process
   begin
      clk <= '1';
      wait for clk_per / 2;
      clk <= '0';
      wait for clk_per /2;
   end process;

   tb: process
      variable addr : std_logic_vector(31 downto 0) := (others => '0');
      variable data : std_logic_vector(31 downto 0);
      variable be :  std_logic_vector(3 downto 0);
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait for 2*clk_per;

      -- Write data to address 0x4
      addr := X"00000004";
      data := X"0123456F";
      be := "1111";
      WriteData(addr, data, be, status(0), 0);

      -- Write data to address 0x8
      addr := X"00000008";
      data := X"0123456E";
      be := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 5*clk_per;

      -- Read and check validity of data in mem
      data := X"00000000";
      addr := X"00000004";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0123456F")  report "Wrong data" severity note;

      delay_drdy <= 0;
      data := X"00000000";
      addr := X"00000008";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0123456E")  report "Wrong data" severity note;

      -- Write file to mem
      wait for 10*clk_per;
      delay_drdy <= 1;
      WriteFileToMem("./example_data.txt", status(0), 0);
      wait for 2*clk_per;

      -- Read and check validity of data in mem
      addr := X"00000000";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000004")  report "Wrong data on address 0x0" severity note;

      delay_drdy <= 0;
      addr := X"00000004";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000008")  report "Wrong data on address 0x4" severity note;

      addr := X"00000008";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0000000C")  report "Wrong data on address 0x8" severity note;


      wait for 5*clk_per;
      delay_drdy <= 0;
      addr := X"00000000";
      WriteFileToMemCont("./example_data_continuos.txt", addr, status(0), 0);

      wait for 5*clk_per;
      addr := X"00000000";
      ReadMemToFileCont("./data_out.txt", addr, 6, status(0), 0);

      -- Write and Read with delays signals

      -- DRDY delay

      delay_drdy <= 2;
      wait for 10*clk_per;
      WriteFileToMem("./example_data.txt", status(0), 0);

      addr := X"0000000A";
      data := X"0123456E";
      be := "1111";
      WriteData(addr, data, be, status(0), 0);
      wait for 2*clk_per;

      addr := X"00000000";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000004")  report "Wrong data on address 0x0" severity note;

      addr := X"00000004";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000008")  report "Wrong data on address 0x4" severity note;

      delay_drdy <= 0;
      addr := X"00000008";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0000000C")  report "Wrong data on address 0x8" severity note;

      addr := X"0000000A";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0123456E")  report "Wrong data on address 0x8" severity note;

      -- wavering DRDY signal

      wait for 10*clk_per;
      delay_drdy <= 0;
      WriteFileToMem("./example_data.txt", status(0), 0);
      wait for 2*clk_per;

      addr := X"00000000";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000004")  report "Wrong data on address 0x0" severity note;

      delay_drdy <= 1;
      addr := X"00000004";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000008")  report "Wrong data on address 0x4" severity note;

      delay_drdy <= 0;
      addr := X"00000008";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0000000C")  report "Wrong data on address 0x8" severity note;
      delay_drdy <= 0;

      -- ARDY delay
      wait for 10*clk_per;
      WriteFileToMem("./example_data.txt", status(0), 0);
      wait for 2*clk_per;

      delay_drdy <= 3;
      delay_ardy <= 3;
      addr := X"00000000";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000004")  report "Wrong data on address 0x0" severity note;

      addr := X"00000004";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"00000008")  report "Wrong data on address 0x4" severity note;
      delay_ardy <= 0;
      delay_drdy <= 0;

      addr := X"00000008";
      be := "1111";
      ReadData(addr, data, be, status(0), 0);
      assert (data = X"0000000C")  report "Wrong data on address 0x8" severity note;

      wait;
   end process;

end architecture;



