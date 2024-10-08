--
-- disp_tb.vhd: Component testbench.
-- Copyright (C) 2003 CESNET
-- Author(s): Martinek Tomas martinek@liberouter.org
--            Pus Viktor xpusvi00@stud.fit.vutbr.cz
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
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant FL_DATA_WIDTH     : integer := 32;

   constant IFC_BYTE_OFFSET   : integer := 5;   -- Starts from 0
   constant IFC_NIBBLE_OFFSET : integer := 1;   -- 0 - low; 1 - high

   -- How much data word to skip before writing reg_ifc_allow.
   constant WORD_COUNT : integer := IFC_BYTE_OFFSET / (FL_DATA_WIDTH/8);

   -- Position of the edit operation within a data word (nibble position)
   constant WORD_POS   : integer :=
      (IFC_BYTE_OFFSET rem (FL_DATA_WIDTH/8)) * 2 + IFC_NIBBLE_OFFSET;


   constant clkper      : time      := 10 ns;
   constant INIT_TIME   : time      := 4*clkper + 10*clkper;
   constant RESET_TIME  : time      := 3*clkper;

   -- TEST behaviour after RESET asserted
   constant TEST_RESET  : boolean := false;

   -- Packet parameters

   -- Number of words in packet
   constant PAC_LENGTH : integer := 32;

   -- Number of packets to send
   constant PAC_NUM    : integer := 16;

   signal clk      : std_logic;
   signal reset    : std_logic;

   signal rx_data      : std_logic_vector(FL_DATA_WIDTH - 1 downto 0);
   signal rx_rem       : std_logic_vector(log2(FL_DATA_WIDTH/8) - 1 downto 0);
   signal rx_src_rdy_n : std_logic;
   signal rx_dst_rdy_n : std_logic;
   signal rx_sop_n     : std_logic;
   signal rx_eop_n     : std_logic;
   signal rx_sof_n     : std_logic;
   signal rx_eof_n     : std_logic;

   signal tx0_data     : std_logic_vector(FL_DATA_WIDTH - 1 downto 0);
   signal tx0_rem      : std_logic_vector(log2(FL_DATA_WIDTH/8) - 1 downto 0);
   signal tx0_src_rdy_n: std_logic;
   signal tx0_dst_rdy_n: std_logic;
   signal tx0_sop_n    : std_logic;
   signal tx0_eop_n    : std_logic;
   signal tx0_sof_n    : std_logic;
   signal tx0_eof_n    : std_logic;

   signal tx1_data     : std_logic_vector(FL_DATA_WIDTH - 1 downto 0);
   signal tx1_rem      : std_logic_vector(log2(FL_DATA_WIDTH/8) - 1 downto 0);
   signal tx1_src_rdy_n: std_logic;
   signal tx1_dst_rdy_n: std_logic;
   signal tx1_sop_n    : std_logic;
   signal tx1_eop_n    : std_logic;
   signal tx1_sof_n    : std_logic;
   signal tx1_eof_n    : std_logic;

   signal tx2_data     : std_logic_vector(FL_DATA_WIDTH - 1 downto 0);
   signal tx2_rem      : std_logic_vector(log2(FL_DATA_WIDTH/8) - 1 downto 0);
   signal tx2_src_rdy_n: std_logic;
   signal tx2_dst_rdy_n: std_logic;
   signal tx2_sop_n    : std_logic;
   signal tx2_eop_n    : std_logic;
   signal tx2_sof_n    : std_logic;
   signal tx2_eof_n    : std_logic;

   signal tx3_data     : std_logic_vector(FL_DATA_WIDTH - 1 downto 0);
   signal tx3_rem      : std_logic_vector(log2(FL_DATA_WIDTH/8) - 1 downto 0);
   signal tx3_src_rdy_n: std_logic;
   signal tx3_dst_rdy_n: std_logic;
   signal tx3_sop_n    : std_logic;
   signal tx3_eop_n    : std_logic;
   signal tx3_sof_n    : std_logic;
   signal tx3_eof_n    : std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   UUT: entity work.fl_switch_1to4
      generic map (
         FL_DATA_WIDTH     => FL_DATA_WIDTH,
         IFC_BYTE_OFFSET   => IFC_BYTE_OFFSET,
         IFC_NIBBLE_OFFSET => IFC_NIBBLE_OFFSET
      )
      port map (
         CLK          => CLK,
         RESET        => RESET,

         -- Write interface
         RX_DATA      => rx_data,
         RX_REM       => rx_rem,
         RX_SRC_RDY_N => rx_src_rdy_n,
         RX_DST_RDY_N => rx_dst_rdy_n,
         RX_SOP_N     => rx_sop_n,
         RX_EOP_N     => rx_eop_n,
         RX_SOF_N     => rx_sof_n,
         RX_EOF_N     => rx_eof_n,

         -- Read interface 0
         TX0_DATA     => tx0_data,
         TX0_REM      => tx0_rem,
         TX0_SRC_RDY_N=> tx0_src_rdy_n,
         TX0_DST_RDY_N=> tx0_dst_rdy_n,
         TX0_SOP_N    => tx0_sop_n,
         TX0_EOP_N    => tx0_eop_n,
         TX0_SOF_N    => tx0_sof_n,
         TX0_EOF_N    => tx0_eof_n,

         -- Read interface 1
         TX1_DATA     => tx1_data,
         TX1_REM      => tx1_rem,
         TX1_SRC_RDY_N=> tx1_src_rdy_n,
         TX1_DST_RDY_N=> tx1_dst_rdy_n,
         TX1_SOP_N    => tx1_sop_n,
         TX1_EOP_N    => tx1_eop_n,
         TX1_SOF_N    => tx1_sof_n,
         TX1_EOF_N    => tx1_eof_n,

         -- Read interface 2
         TX2_DATA     => tx2_data,
         TX2_REM      => tx2_rem,
         TX2_SRC_RDY_N=> tx2_src_rdy_n,
         TX2_DST_RDY_N=> tx2_dst_rdy_n,
         TX2_SOP_N    => tx2_sop_n,
         TX2_EOP_N    => tx2_eop_n,
         TX2_SOF_N    => tx2_sof_n,
         TX2_EOF_N    => tx2_eof_n,

         -- Read interface 3
         TX3_DATA     => tx3_data,
         TX3_REM      => tx3_rem,
         TX3_SRC_RDY_N=> tx3_src_rdy_n,
         TX3_DST_RDY_N=> tx3_dst_rdy_n,
         TX3_SOP_N    => tx3_sop_n,
         TX3_EOP_N    => tx3_eop_n,
         TX3_SOF_N    => tx3_sof_n,
         TX3_EOF_N    => tx3_eof_n
      );

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;


-- Data input generator -------------------------------
digen: process
begin
   RX_DATA        <= (others =>'0');
   RX_REM         <= (others => '0');
   RX_SOP_N       <= '1';
   RX_EOP_N       <= '1';
   RX_SOF_N       <= '1';
   RX_EOF_N       <= '1';
   RX_SRC_RDY_N   <= '1';

   wait for RESET_TIME + INIT_TIME;

   RX_SRC_RDY_N <= '0';

   for pnum in 1 to PAC_NUM - 1 loop
      for ppart in 0 to PAC_LENGTH - 1 loop
         -- Generate SOF/EOF on the packet edges
         if (ppart = 0) then
            RX_SOF_N <= '0';
         else
            RX_SOF_N <= '1';
         end if;

         if (ppart = PAC_LENGTH - 1) then
            RX_EOF_N <= '0';
         else
            RX_EOF_N <= '1';
         end if;


         RX_DATA <= conv_std_logic_vector(ppart, rx_data'length);

         -- Fill switch information into the word at appropriate place
         if (ppart = WORD_COUNT) then
            RX_DATA((WORD_POS+1)*4 - 1 downto WORD_POS*4) <=
               conv_std_logic_vector(pnum, 4);
         end if;

         wait for clkper;
         wait until clk'event and clk = '1' and RX_DST_RDY_N = '0';
      end loop;
   end loop;

   RX_SRC_RDY_N <= '1';
   wait;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
   reset <= '1';

   TX0_DST_RDY_N <= '1';
   TX1_DST_RDY_N <= '1';
   TX2_DST_RDY_N <= '1';
   TX3_DST_RDY_N <= '1';


   wait for RESET_TIME;
   reset <= '0';

   TX0_DST_RDY_N <= '0';
   TX1_DST_RDY_N <= '0';
   TX2_DST_RDY_N <= '0';
   TX3_DST_RDY_N <= '0';


   for i in 1 to PAC_NUM - 1 loop
      wait until RX_SOF_N = '0';

      if (TEST_RESET = true) then
         wait for 3600 ns;

         reset <= '1';
         wait for RESET_TIME + clkper/6;
         reset <= '0';
      else

         if (i = 8) then
            -- Test situation when the others are waiting for one interface
            TX2_DST_RDY_N <= '1';
            wait for i*clkper;
            TX0_DST_RDY_N <= '0';
            TX1_DST_RDY_N <= '0';
            TX2_DST_RDY_N <= '0';
            TX3_DST_RDY_N <= '0';
         else
            TX0_DST_RDY_N <= '1';
            TX1_DST_RDY_N <= '1';
            TX2_DST_RDY_N <= '1';
            TX3_DST_RDY_N <= '1';
            wait for i*clkper;
            TX0_DST_RDY_N <= '0';
            TX1_DST_RDY_N <= '0';
            TX2_DST_RDY_N <= '0';
            TX3_DST_RDY_N <= '0';
         end if;

      end if;

   end loop;

   wait;
end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
