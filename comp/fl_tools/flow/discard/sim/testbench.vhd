-- testbench.vhd: FrameLink Discard testbench file
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;
use work.mi32_pkg.all;
use work.ib_sim_oper.all; -- Internal Bus Simulation Package

entity testbench is
end testbench;

architecture testbench of testbench is

constant CLKPER         : time      := 10 ns;
constant RESET_TIME     : time      := 20 * CLKPER;
constant DATA_WIDTH     : integer   := 64;
constant STATUS_WIDTH   : integer   := 8;
constant CHANNELS       : integer   := 3;
constant CHAN_WIDTH     : integer   := log2(CHANNELS);
constant CNT_WIDTH      : integer   := 64;

signal clk           : std_logic;
signal reset         : std_logic;

signal rx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal rx_drem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal rx_sof_n     : std_logic;
signal rx_eof_n     : std_logic;
signal rx_sop_n     : std_logic;
signal rx_eop_n     : std_logic;
signal rx_src_rdy_n : std_logic;
signal rx_dst_rdy_n : std_logic_vector(CHANNELS-1 downto 0);

signal rx_chan      : std_logic_vector(CHAN_WIDTH-1 downto 0);

signal tx_data      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal tx_drem      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
signal tx_sof_n     : std_logic;
signal tx_eof_n     : std_logic;
signal tx_sop_n     : std_logic;
signal tx_eop_n     : std_logic;
signal tx_src_rdy_n : std_logic;
signal tx_dst_rdy_n : std_logic;

signal tx_chan      : std_logic_Vector(CHAN_WIDTH-1 downto 0);

signal status       : std_logic_vector(CHANNELS*STATUS_WIDTH-1 downto 0);
signal zeros        : std_logic_vector(CHANNELS*STATUS_WIDTH-1 downto 0);
signal ones         : std_logic_vector(CHANNELS*STATUS_WIDTH-1 downto 0);

signal mi           : t_mi32;
signal ib_sim_ctrl         : t_ib_ctrl;
signal ib_sim_strobe       : std_logic;
signal ib_sim_busy         : std_logic;

begin

uut: entity work.FL_DISCARD_STAT
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      CHANNELS       => CHANNELS,
      STATUS_WIDTH   => STATUS_WIDTH,
      CNT_WIDTH      => CNT_WIDTH,
      COUNT_DROP     => true,
      COUNT_PASS     => true,
      COUNT_DROP_LEN => true,
      COUNT_PASS_LEN => true
   )
   port map(
      CLK            => clk,
      RESET          => reset,
      --
      RX_DATA        => rx_data,
      RX_DREM        => rx_drem,
      RX_SOF_N       => rx_sof_n,
      RX_EOF_N       => rx_eof_n,
      RX_SOP_N       => rx_sop_n,
      RX_EOP_N       => rx_eop_n,
      RX_SRC_RDY_N   => rx_src_rdy_n,
      RX_DST_RDY_N   => rx_dst_rdy_n,

      RX_CHAN        => rx_chan,
      --
      TX_DATA        => tx_data,
      TX_DREM        => tx_drem,
      TX_SOF_N       => tx_sof_n,
      TX_EOF_N       => tx_eof_n,
      TX_SOP_N       => tx_sop_n,
      TX_EOP_N       => tx_eop_n,
      TX_SRC_RDY_N   => tx_src_rdy_n,
      --TX_DST_RDY_N   => tx_dst_rdy_n,

      TX_CHAN        => tx_chan,

      STATUS         => status,

      MI_DWR         => mi.dwr,
      MI_ADDR        => mi.addr,
      MI_BE          => mi.be,
      MI_RD          => mi.rd,
      MI_WR          => mi.wr,
      MI_DRDY        => mi.drdy,
      MI_ARDY        => mi.ardy,
      MI_DRD         => mi.drd
   );

MI32_SIM_U : entity work.MI32_SIM
   generic map (
      UPSTREAM_LOG_FILE   => "ib_upstream_log.txt",
      DOWNSTREAM_LOG_FILE => "ib_downstream_log.txt",
      BASE_ADDR           => X"00001000",
      LIMIT               => X"00001000",
      FREQUENCY           => 100,
      BUFFER_EN           => false
   )
   port map (
      -- Common interface
      IB_RESET           => reset,
      IB_CLK             => clk,

      -- User Component Interface
      CLK                => clk,
      MI32               => mi,

      -- IB SIM interface
      CTRL               => ib_sim_ctrl,
      STROBE             => ib_sim_strobe,
      BUSY               => ib_sim_busy
   );

clkgen: process
begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
end process;

reset_gen : process
begin
   RESET <= '1';
   wait for RESET_TIME;
   wait for 1 ns;
   RESET <= '0';
   wait;
end process reset_gen;

tb: process

-- Support for ib_op
procedure ib_op(ctrl : in t_ib_ctrl) is
begin
   wait until (CLK'event and CLK='1' and ib_sim_busy = '0');
   ib_sim_ctrl <= ctrl;
   ib_sim_strobe <= '1';
   wait until (CLK'event and CLK='1');
   ib_sim_strobe <= '0';
end ib_op;

begin
   zeros <= (others => '0');
   ones <= (others => '1');

   wait for clkper;
   --tx_dst_rdy_n <= '0';

   rx_data <= conv_std_logic_vector(100, DATA_WIDTH);
   rx_drem <= conv_std_logic_vector(DATA_WIDTH/8 - 1, log2(DATA_WIDTH/8));
   rx_src_rdy_n <= '1';
   rx_sop_n <= '0';
   rx_sof_n <= '0';
   rx_eop_n <= '1';
   rx_eof_n <= '1';

   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);

   status <= zeros(CHANNELS*STATUS_WIDTH-1 downto STATUS_WIDTH) &
             conv_std_logic_vector((2**(STATUS_WIDTH-1))-12, STATUS_WIDTH);

   wait for 2*RESET_TIME;
   wait for 1 ns;


   rx_src_rdy_n <= '0';
   -- Send first frame, advertised length 100, channel 1
   rx_data <= conv_std_logic_vector(1*(2**16) + 100, DATA_WIDTH);
   rx_sop_n <= '0';
   rx_sof_n <= '0';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper; -- sof, sop
   -- First frame, second word
   rx_data <= conv_std_logic_vector(2*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_sof_n <= '1';
   rx_sop_n <= '1';
   wait for clkper; -- eop
   -- First frame, third word
   rx_data <= conv_std_logic_vector(3*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '1';
   rx_sop_n <= '0';
   wait for clkper; -- sop

   rx_data <= conv_std_logic_vector(4*(2**16) + 100, DATA_WIDTH);
   rx_sop_n <= '1';
   wait for clkper;

   rx_data <= conv_std_logic_vector(5*(2**16) + 100, DATA_WIDTH);
   wait for clkper;

   rx_data <= conv_std_logic_vector(6*(2**16) + 100, DATA_WIDTH);
   wait for clkper;

   rx_data <= conv_std_logic_vector(7*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_eof_n <= '0';
   wait for clkper; -- eof, eop

   rx_src_rdy_n <= '1';
   rx_eop_n <= '1';
   rx_eof_n <= '1';
   wait for clkper; -- Frame end

   wait for 5*clkper;

   rx_src_rdy_n <= '0';
   -- Send first frame, advertised length 100, channel 0
   rx_data <= conv_std_logic_vector(1*(2**16) + 100, DATA_WIDTH);
   rx_sop_n <= '0';
   rx_sof_n <= '0';
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper; -- sof, sop
   -- Send first frame, advertised length 100, channel 1
   rx_data <= conv_std_logic_vector(1*(2**20) + 100, DATA_WIDTH);
   rx_src_rdy_n <= '0';
   rx_sop_n <= '0';
   rx_sof_n <= '0';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper; -- sof, sop
   -- First frame, second word, channel 0
   rx_data <= conv_std_logic_vector(2*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_sof_n <= '1';
   rx_sop_n <= '1';
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper; -- eop
   -- First frame, second word, channel 1
   rx_data <= conv_std_logic_vector(2*(2**20) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_sof_n <= '1';
   rx_sop_n <= '1';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper; -- eop
   -- First frame, third word, channel 0
   rx_data <= conv_std_logic_vector(3*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '1';
   rx_sop_n <= '0';
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper; -- sop
   -- First frame, third word, channel 1
   rx_data <= conv_std_logic_vector(3*(2**20) + 100, DATA_WIDTH);
   rx_eop_n <= '1';
   rx_sop_n <= '0';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper; -- sop

   rx_data <= conv_std_logic_vector(4*(2**16) + 100, DATA_WIDTH);
   rx_sop_n <= '1';
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper;
   rx_data <= conv_std_logic_vector(4*(2**20) + 100, DATA_WIDTH);
   rx_sop_n <= '1';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper;

   rx_data <= conv_std_logic_vector(5*(2**16) + 100, DATA_WIDTH);
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper;
   rx_data <= conv_std_logic_vector(5*(2**20) + 100, DATA_WIDTH);
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper;

   rx_data <= conv_std_logic_vector(6*(2**16) + 100, DATA_WIDTH);
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper;
   rx_data <= conv_std_logic_vector(6*(2**20) + 100, DATA_WIDTH);
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper;

   rx_data <= conv_std_logic_vector(7*(2**16) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_eof_n <= '0';
   rx_chan <= conv_std_logic_vector(0, CHAN_WIDTH);
   wait for clkper; -- eof, eop
   rx_data <= conv_std_logic_vector(7*(2**20) + 100, DATA_WIDTH);
   rx_eop_n <= '0';
   rx_eof_n <= '0';
   rx_chan <= conv_std_logic_vector(1, CHAN_WIDTH);
   wait for clkper; -- eof, eop

   rx_src_rdy_n <= '1';
   rx_eop_n <= '1';
   rx_eof_n <= '1';
   wait for clkper; -- Frame end

   -- Read number of dropped frames at channel 0
   ib_op(ib_local_read(X"00001000",  -- src addr
                       X"00000002", -- dst addr
                       4,          -- length
                       16#ABAB#));  -- tag
   ib_op(ib_local_read(X"00010004", X"00000002", 4, 16#ABAB#));

   -- Read number of dropped frames at channel 1
   ib_op(ib_local_read(X"00001008", X"00000002", 4, 16#ABAB#));
   ib_op(ib_local_read(X"0000100C", X"00000002", 4, 16#ABAB#));


   -- Read number of passed frames at channel 0
   ib_op(ib_local_read(X"00001200", X"00000002", 4, 16#ABAB#));
   ib_op(ib_local_read(X"00001204", X"00000002", 4, 16#ABAB#));

   -- Read number of passed frames at channel 1
   ib_op(ib_local_read(X"00001208", X"00000002", 4, 16#ABAB#));
   ib_op(ib_local_read(X"0000120C", X"00000002", 4, 16#ABAB#));

   -- Read length of dropped frames at channel 0
   ib_op(ib_local_read(X"00001400", X"00000002", 4, 16#ABAB#));
   ib_op(ib_local_read(X"00001404", X"00000002", 4, 16#ABAB#));

   -- Read length of passed frames at channel 0
   ib_op(ib_local_read(X"00001600", X"00000002", 4, 16#ABAB#));
   ib_op(ib_local_read(X"00001604", X"00000002", 4, 16#ABAB#));


   -- Write into command register to reset counters
   ib_op(ib_local_write(X"00001800",   -- dst addr
                        X"00000000",   -- src addr
                        4,             -- length
                        16#ABAB#,      -- tag
                        '0',           -- No completition ack
                        X"0000000000000003")); -- data

   -- Read status register
   ib_op(ib_local_read(X"00001800", X"00000002", 4, 16#ABAB#));

   -- Write into command register to stop counting
   ib_op(ib_local_write(X"00001800", X"00000000", 4, 16#ABAB#, '0',
                        X"0000000000000000"));



   wait;
   end process;

end;
