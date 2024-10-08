-- cam_tb.vhd: Testbench for CAM
-- Copyright (C) 2005 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_tb of testbench is

   constant CAM_ROW_WIDTH   : integer := 18;
   constant CAM_ROW_COUNT   : integer := 16;
   constant CAM_ADDR_WIDTH  : integer := 8;
   constant CAM_ELEM_WIDTH  : integer := 6;
   constant SEQUENCED_SEARCH: integer := 3;
   constant USE_UNMATCHABLE : boolean := true;

   constant clk_period      : time    := 10 ns;
   constant WAIT_BETWEEN_SEARCH:integer:= 0;

-- ------------------ Signals declaration -------------------------------------
   signal ADDR              : std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
   signal DATA_IN           : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal MASK_IN           : std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
   signal WRITE_ENABLE      : std_logic;
   signal MATCH_ENABLE      : std_logic;
   signal MATCH_RDY         : std_logic;
   signal MATCH_RST         : std_logic;
   signal RESET             : std_logic;
   signal CLK               : std_logic;
   signal MATCH_BUS         : std_logic_vector((CAM_ROW_COUNT - 1) downto 0);
   signal MATCH_BUS_VLD     : std_logic;

begin

-- ---------- Connecting component to testbench  ------------------------------
   UUT : entity work.CAM
      generic map (
         CAM_ROW_WIDTH  => CAM_ROW_WIDTH,
         CAM_ROW_COUNT  => CAM_ROW_COUNT,
         CAM_ADDR_WIDTH => CAM_ADDR_WIDTH,
         ELEM_WIDTH     => CAM_ELEM_WIDTH,
         SEQUENCED_SEARCH=>SEQUENCED_SEARCH,
         USE_UNMATCHABLE=> USE_UNMATCHABLE
      )
      port map (
         ADDR              => ADDR,
         DATA_IN           => DATA_IN,
         MASK_IN           => MASK_IN,
         WRITE_EN          => WRITE_ENABLE,
         MATCH_EN          => MATCH_ENABLE,
         MATCH_RDY         => MATCH_RDY,
         MATCH_RST         => MATCH_RST,
         RESET             => RESET,
         CLK               => CLK,
         MATCH_BUS         => MATCH_BUS,
         MATCH_BUS_VLD     => MATCH_BUS_VLD
      );

-- ----------- Generating clock signal ----------------------------------------
   tb_clk_gen: process
   begin
      CLK <= '1';
      wait for clk_period/2;
      CLK <= '0';
      wait for clk_period/2;
   end process tb_clk_gen;

-- ----------- Probes ---------------------------------------------------------
   probe : process
-- ----------------------------------------------------------------
--                    Procedures declaration
-- ----------------------------------------------------------------

-- ----------------------------------------------------------------
-- procedure cam_insert_word inserts one word into CAM data array in the row
-- selected by address
--
-- Parameters:
--    p_addr:     data row address
--    p_data_in:  inserted data
--    p_mask_in:  specify 'care' and 'dont't care' bits
--                '1' => I care about that bit
--                '0' => I don't care about that bit
--
      procedure cam_insert_word(
         p_addr     : in std_logic_vector((CAM_ADDR_WIDTH - 1) downto 0);
         p_data_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0);
         p_mask_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         wait for 1 ns;
         WRITE_ENABLE <= '1';
         ADDR     <= p_addr;
         DATA_IN  <= p_data_in;
         MASK_IN  <= p_mask_in;
         wait for clk_period;
         WRITE_ENABLE <= '0';
         wait for 64*clk_period;
         wait until clk'event and clk='1';
         wait for 1 ns;
      end cam_insert_word;

-- ----------------------------------------------------------------
-- procedure cam_search_word searches in CAM for selected data
--
-- Parameters:
--    p_data_in:     data that should be searched in CAM
--
      procedure cam_search_word(
         p_data_in  : in std_logic_vector((CAM_ROW_WIDTH - 1) downto 0)
      ) is
      begin
         wait until clk'event and clk='1';
         wait for 1 ns;
         MATCH_ENABLE <= '1';
         DATA_IN  <= p_data_in;
         wait for clk_period;
         MATCH_ENABLE <= '0';
      end cam_search_word;

   begin
-- ----------- Activating RESET signal ----------------------------------------
   RESET <= '1';
   wait for 10*clk_period;
   wait until CLK'event and CLK='1';

   RESET <= '0';

   MATCH_RST <= '0';
   WRITE_ENABLE <= '0';
   MATCH_ENABLE <= '0';
   MASK_IN  <= "000000000000000000";
   ADDR     <= "00000000";
   DATA_IN  <= "000000000000000000";

   wait for clk_period;
   wait until CLK'event and CLK='1';
   wait for 1 ns;

-- ----------- Fill memory elements -------------------------------------------

-- Try simple inserting (without using MASK)
   cam_insert_word("00000000","000000000000000000","111111111111111111");
   cam_insert_word("00000001","000000000011111111","111111111111111111");
   cam_insert_word("00000010","000000000011110000","111111111111111111");
   cam_insert_word("00000011","000000000000001111","111111111111111111");
   cam_insert_word("00000100","000000000010101010","111111111111111111");
   cam_insert_word("00000101","000000000001010101","111111111111111111");
   cam_insert_word("00000110","000000000011001100","111111111111111111");
   cam_insert_word("00000111","000000000000110011","111111111111111111");
   cam_insert_word("00001000","000000000011000011","111111111111111111");
   cam_insert_word("00001001","000000000000111100","111111111111111111");
   cam_insert_word("00001010","000000000001000010","111111111111111111");
   cam_insert_word("00001011","000000000001100110","111111111111111111");

-- Try advanced inserting (specifying MASK)
   cam_insert_word("00001100","000000000010101010","111111111110101010");
      -- 1d1d1d1d
   cam_insert_word("00001101","000000000011110000","111111111111110000");
      -- 1111dddd
   cam_insert_word("00001110","000000000000001111","111111111100001111");
      -- dddd1111
   cam_insert_word("00001111","000000000000000001","111111111100000000");
      -- dddddddu (LSB is unmatchable, because data=1 and mask=0)

-- ----------- Try memory elements --------------------------------------------
   wait for 5*clk_period;
   wait until clk'event and clk='1';
   wait for 1 ns;

   cam_search_word("000000000000000000");
   wait until MATCH_BUS_VLD = '1';
   wait for 0.5*clk_period; -- this wait is here only for testing purposes (so that
                        -- assertion will work)
   assert (MATCH_BUS="0000000000000001")
      report "Search #1 FAILED!!!" severity error;

   wait for WAIT_BETWEEN_SEARCH*clk_period;
   cam_search_word("000000000011111111");
   wait until MATCH_BUS_VLD = '1';
   wait for 0.5*clk_period;
   assert (MATCH_BUS="0111000000000010")
      report "Search #2 FAILED!!!" severity error;

   wait for WAIT_BETWEEN_SEARCH*clk_period;
   cam_search_word("000000000010101010");
   wait until MATCH_BUS_VLD = '1';
   wait for 0.5*clk_period;
   assert (MATCH_BUS="0001000000010000")
      report "Search #3 FAILED!!!" severity error;

   wait for WAIT_BETWEEN_SEARCH*clk_period;
   cam_search_word("000000000001010101");
   wait until MATCH_BUS_VLD = '1';
   wait for 0.5*clk_period;
   assert (MATCH_BUS="0000000000100000")
      report "Search #4 FAILED!!!" severity error;

   wait;
   end process probe;

end cam_tb;
