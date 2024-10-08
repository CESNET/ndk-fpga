-- fl_rxbuffer_tb.vhd: Testbench for FrameLink RX Buffer
-- Copyright (C) 2003 CESNET
-- Author(s): Libor Polcak <xpolca03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;
use work.math_pack.all;
use work.mi32_pkg.all;
use work.ib_sim_oper.all;
use work.fl_sim_oper.all; -- FrameLink Simulation Package

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
   -- Constant declaration
   constant DATA_WIDTH         : integer := 128;
   constant USE_BRAMS          : boolean := True;
   constant ITEMS              : integer := 4;
   constant PARTS              : integer := 3;

   constant clkper             : time := 10 ns;
   constant reset_time         : time := 100 ns;
   constant idle_time          : time := 150 ns;
   constant wait_time          : time := 50 ns;

   -- Signals declaration
   signal clk                  : std_logic;
   signal reset                : std_logic;

   -- UUT input signals
   signal rx_buffer_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal rx_buffer_rem        :
                           std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
   signal rx_buffer_sof_n      : std_logic;
   signal rx_buffer_sop_n      : std_logic;
   signal rx_buffer_eop_n      : std_logic;
   signal rx_buffer_eof_n      : std_logic;
   signal rx_buffer_src_rdy_n  : std_logic;
   signal rx_buffer_dst_rdy_n  : std_logic;

   -- FL Sim signals
   signal filename             : t_fl_ctrl;
   signal fl_sim_strobe        : std_logic;
   signal fl_sim_busy          : std_logic;

   -- MI32 Sim signals
   signal mi32_sim_ctrl        : t_ib_ctrl;
   signal mi32_sim_strobe      : std_logic;
   signal mi32_sim_busy        : std_logic;

   -- MI32 connection between fl_rxbuffer and mi32_sim
   signal mi32_connection      : t_mi32;
-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin
   -- -------------------------------------------------------------------------
   --                   FL RX Buffer
   -- -------------------------------------------------------------------------
   uut: entity work.FL_RXBUFFER
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         USE_BRAMS      => USE_BRAMS,
         PARTS          => PARTS,
         ITEMS          => ITEMS
      )
      port map (
         CLK            => clk,
         RESET          => reset,

         -- Frame Link input
         RX_DATA        => rx_buffer_data,
         RX_REM         => rx_buffer_rem,
         RX_SOF_N       => rx_buffer_sof_n,
         RX_SOP_N       => rx_buffer_sop_n,
         RX_EOP_N       => rx_buffer_eop_n,
         RX_EOF_N       => rx_buffer_eof_n,
         RX_SRC_RDY_N   => rx_buffer_src_rdy_n,
         RX_DST_RDY_N   => rx_buffer_dst_rdy_n,

         -- MI32 in/out interface
         MI32           => mi32_connection
      );

   -- -------------------------------------------------------------------------
   --                   MI32 Simulation Component
   -- -------------------------------------------------------------------------
   mi32_sim: entity work.MI32_SIM
      generic map (
         UPSTREAM_LOG_FILE   => "./mi32.upstream",
         DOWNSTREAM_LOG_FILE => "./mi32.downstream",
         BASE_ADDR           => X"00000000",
         LIMIT               => X"00000020",
         BUFFER_EN           => false
      )
      port map (
         -- Common interface
         IB_RESET            => reset,
         IB_CLK              => clk,

         -- User Component Interface
         CLK                 => clk,
         MI32                => mi32_connection,

         -- IB SIM interface
         STATUS              => open,
         CTRL                => mi32_sim_ctrl,
         STROBE              => mi32_sim_strobe,
         BUSY                => mi32_sim_busy
     );

   -- -------------------------------------------------------------------------
   --                   FL Simulation Component
   -- -------------------------------------------------------------------------
   fl_sim: entity work.FL_SIM
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         RX_LOG_FILE    => "",
         FRAME_PARTS    => PARTS,
         TX_LOG_FILE    => "fl_sim_tx.txt"
      )
      port map (
         -- Common interface
         FL_RESET       => reset,
         FL_CLK         => clk,

         -- Frame link Interface
         RX_DATA        => (others => '0'),
         RX_REM         => (others => '0'),
         RX_SOF_N       => '1',
         RX_EOF_N       => '1',
         RX_SOP_N       => '1',
         RX_EOP_N       => '1',
         RX_SRC_RDY_N   => '1', -- Source isn't ready
         RX_DST_RDY_N   => open,

         TX_DATA        => rx_buffer_data,
         TX_REM         => rx_buffer_rem,
         TX_SOF_N       => rx_buffer_sof_n,
         TX_EOF_N       => rx_buffer_eof_n,
         TX_SOP_N       => rx_buffer_sop_n,
         TX_EOP_N       => rx_buffer_eop_n,
         TX_SRC_RDY_N   => rx_buffer_src_rdy_n,
         TX_DST_RDY_N   => rx_buffer_dst_rdy_n,

         -- FL SIM interface
         CTRL           => filename,
         STROBE         => fl_sim_strobe,
         BUSY           => fl_sim_busy
      );

   -- ----------------------------------------------------
   -- CLK generator
   clkgen: process
   begin
      clk <= '1';
      wait for clkper/2;
      clk <= '0';
      wait for clkper/2;
   end process;

   resetgen: process
   begin
      reset <= '1';
      wait for reset_time;
      reset <= '0';
      wait;
   end process;

   tb: process
      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessery for corect function of FL_SIM
      procedure fl_op(ctrl : in t_fl_ctrl) is
      begin
         wait until (clk'event and clk='1' and fl_sim_busy = '0');
         filename <= ctrl;
         fl_sim_strobe <= '1';
         wait until (clk'event and clk='1');
         fl_sim_strobe <= '0';
      end fl_op;

      -- This procedure must be placed in this testbench file. Using this
      -- procedure is necessary for correct function of MI32_SIM
      procedure ib_op(ctrl : in t_ib_ctrl) is
      begin
         wait until (clk'event and clk='1' and mi32_sim_busy = '0');
         mi32_sim_ctrl <= ctrl;
         mi32_sim_strobe <= '1';
         wait until (clk'event and clk='1');
         mi32_sim_strobe <= '0';
      end ib_op;


   begin
      fl_sim_strobe <= '0';
      wait for idle_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001")); -- RXB Start
      fl_op(fl_send32("./fl_sim_send.txt"));
      wait for wait_time;
      ib_op(ib_local_read(X"00000004", X"11111111", 1, 16#ABAB#)); -- RXB Status
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000008", X"11111111", 1, 16#ABAB#)); -- read fl signals
      wait for wait_time;
      ib_op(ib_local_read(X"0000000C", X"11111111", 1, 16#ABAB#)); -- read fl rem
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_read(X"00000000", X"11111111", 1, 16#ABAB#)); -- read cmd reg
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000001")); -- RXB Start
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      ib_op(ib_local_write(X"00000000", X"11111111", 1, 16#ABAB#, '0', X"0000000000000003")); -- RXB Get Item
      wait for wait_time;
      ib_op(ib_local_read(X"00000010", X"11111111", 1, 16#ABAB#)); -- read fl data (31 downto 0)
      wait for wait_time;
      ib_op(ib_local_read(X"00000014", X"11111111", 1, 16#ABAB#)); -- read fl data (63 downto 32)
      wait for wait_time;
      ib_op(ib_local_read(X"00000018", X"11111111", 1, 16#ABAB#)); -- read fl data (95 downto 64)
      wait for wait_time;
      ib_op(ib_local_read(X"0000001C", X"11111111", 1, 16#ABAB#)); -- read fl data (127 downto 96)
      wait for wait_time;
      wait;
   end process;
end architecture behavioral;
