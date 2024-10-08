-- testbench.vhd: FL_ASFIFO testbench
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;
use ieee.std_logic_arith.all;

library work;
use work.math_pack.all;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS


-- simulation constants
constant CLKPER_RX   : time      := 8 ns;
constant CLKPER_TX   : time      := 5 ns;
constant WIDTH       : integer   := 64;
constant DREM        : integer   := max(log2(WIDTH)-4, 0)+1;

-- signals from/to tested unit
signal RX_CLK        : std_logic;
signal RX_RESET      : std_logic;
signal TX_CLK        : std_logic;
signal TX_RESET      : std_logic;

-- Change between these four signals based on which of fifos are you about to simulate
--signal RX_DATA       : std_logic_vector(63 downto 0);
--signal RX_DATA       : std_logic_vector(15 downto 0);
signal RX_DATA       : std_logic_vector(WIDTH-1 downto 0);

--signal RX_REM        : std_logic_vector(2 downto 0);
--signal RX_REM        : std_logic_vector(0 downto 0);
signal RX_REM        : std_logic_vector(DREM-1 downto 0);

signal RX_SRC_RDY_N  : std_logic;
signal RX_DST_RDY_N  : std_logic;
signal RX_SOP_N      : std_logic;
signal RX_EOP_N      : std_logic;
signal RX_SOF_N      : std_logic;
signal RX_EOF_N      : std_logic;

-- Change between these four signals based on which of fifos are you about to simulate
--signal TX_DATA       : std_logic_vector(63 downto 0);
--signal TX_DATA       : std_logic_vector(15 downto 0);
signal TX_DATA       : std_logic_vector(WIDTH-1 downto 0);

--signal TX_REM        : std_logic_vector(2 downto 0);
--signal TX_REM        : std_logic_vector(0 downto 0);
signal TX_REM        : std_logic_vector(DREM-1 downto 0);

signal TX_SRC_RDY_N  : std_logic;
signal TX_DST_RDY_N  : std_logic;
signal TX_SOP_N      : std_logic;
signal TX_EOP_N      : std_logic;
signal TX_SOF_N      : std_logic;
signal TX_EOF_N      : std_logic;

begin

-- Unit under test
-- Choose right entity based on which of fifos are you about to simulate
--uut: entity work.FL_ASFIFO_CV2_64B
--uut: entity work.FL_ASFIFO_CV2_16B
--uut: entity work.FL_ASFIFO_CV2_128
uut: entity work.FL_ASFIFO_VIRTEX5
port map(
   TX_CLK      => TX_CLK,
   TX_RESET    => TX_RESET,
   RX_CLK      => RX_CLK,
   RX_RESET    => RX_RESET,

   TX_DATA       => TX_DATA,
   TX_REM        => TX_REM,
   TX_SRC_RDY_N  => TX_SRC_RDY_N,
   TX_DST_RDY_N  => TX_DST_RDY_N,
   TX_SOP_N      => TX_SOP_N,
   TX_EOP_N      => TX_EOP_N,
   TX_SOF_N      => TX_SOF_N,
   TX_EOF_N      => TX_EOF_N,

   RX_DATA       => RX_DATA,
   RX_REM        => RX_REM,
   RX_SRC_RDY_N  => RX_SRC_RDY_N,
   RX_DST_RDY_N  => RX_DST_RDY_N,
   RX_SOP_N      => RX_SOP_N,
   RX_EOP_N      => RX_EOP_N,
   RX_SOF_N      => RX_SOF_N,
   RX_EOF_N      => RX_EOF_N
);

-- Clock generation
tx_clock: process
begin
   TX_CLK <= '1';
   wait for clkper_tx/2;
   TX_CLK <= '0';
   wait for clkper_tx/2;
end process;

rx_clock: process
begin
   RX_CLK <= '1';
   wait for clkper_rx/2;
   RX_CLK <= '0';
   wait for clkper_rx/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   RX_RESET       <= '1';
   TX_RESET       <= '1';
   RX_DATA     <= (others => '0');
   RX_REM      <= (others => '0');
   RX_SRC_RDY_N  <= '1';
   RX_SOP_N      <= '1';
   RX_EOP_N      <= '1';
   RX_SOF_N      <= '1';
   RX_EOF_N      <= '1';
   TX_DST_RDY_N  <= '1';

   wait for 4*clkper_rx;
   RX_RESET <= '0';
   TX_RESET <= '0';
   wait for 4*clkper_rx;

   -- Send frame
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(10, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   TX_DST_RDY_N <= '0';
   wait for clkper_rx;  -- SOF, SOP

   RX_DATA  <= conv_std_logic_vector(11, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(12, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(13, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(14, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(15, RX_DATA'length);
   wait for clkper_rx;

   RX_DATA  <= conv_std_logic_vector(16, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper_rx;  -- EOF, SOP, EOP

   RX_SRC_RDY_N <= '1';
   wait for clkper_rx;


wait;
end process;

end;
