-- testbench.vhd: fl_watch testbench
-- Copyright (C) 2006 CESNET
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
use work.math_pack.all;

library work;

ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

constant clkper :time := 10 ns;
constant INTERFACES : integer := 3;

signal CLK            : std_logic;
signal RESET          : std_logic;
signal SOF_N          : std_logic_vector(INTERFACES-1 downto 0);
signal EOF_N          : std_logic_vector(INTERFACES-1 downto 0);
signal SOP_N          : std_logic_vector(INTERFACES-1 downto 0);
signal EOP_N          : std_logic_vector(INTERFACES-1 downto 0);
signal DST_RDY_N      : std_logic_vector(INTERFACES-1 downto 0);
signal SRC_RDY_N      : std_logic_vector(INTERFACES-1 downto 0);

signal MI_DWR         : std_logic_vector(31 downto 0);
signal MI_ADDR       : std_logic_vector(31 downto 0);
signal MI_RD          : std_logic;
signal MI_WR         : std_logic;
signal MI_BE         : std_logic_vector(3 downto 0);
signal MI_DRD         : std_logic_vector(31 downto 0);
signal MI_ARDY       : std_logic;
signal MI_DRDY       : std_logic;

begin

uut: entity work.fl_watch_norec
generic map(
   INTERFACES  => INTERFACES,
   CNTR_WIDTH  => 33,
   PIPELINE_LEN=> 1,
   GUARD       => true,
   HEADER      => true,
   FOOTER      => true,
   SAMPLE      => true,
   CHECK_PARTS => true
)
port map(
CLK            => CLK,
RESET          => RESET,
SOF_N          => SOF_N,
EOF_N          => EOF_N,
SOP_N          => SOP_N,
EOP_N          => EOP_N,
DST_RDY_N      => DST_RDY_N,
SRC_RDY_N      => SRC_RDY_N,

MI_DWR         => MI_DWR,
MI_ADDR        => MI_ADDR,
MI_RD        => MI_RD,
MI_WR        => MI_WR,
MI_BE        => MI_BE,
MI_DRD          => MI_DRD,
MI_ARDY         => MI_ARDY,
MI_DRDY         => MI_DRDY
);

-- Clock generation
local_clock: process
begin
   CLK <= '1';
   wait for clkper/2;
   CLK <= '0';
   wait for clkper/2;
end process;

-- Test process
test: process
begin
   wait for 2 ns;
   SOF_N <= "111";
   EOF_N <= "111";
   SOP_N <= "111";
   EOP_N <= "111";
   DST_RDY_N <= "111";
   SRC_RDY_N <= "111";

   MI_DWR <= (others => '0');
   MI_ADDR <= (others => '0');
   MI_RD <= '0';
   MI_WR <= '0';
   MI_BE <= "0000";

   RESET <= '1';
   wait for 5*clkper;
   RESET <= '0';
   wait for 5*clkper;

   SRC_RDY_N <= "101";  -- Interface 1, valid frame, 1 part, only 1 cycle
   DST_RDY_N <= "101";
   SOF_N <= "101";
   SOP_N <= "101";
   EOF_N <= "101";
   EOP_N <= "101";      -- SOF, SOP, EOF, EOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";
   EOF_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";
   wait for 3*clkper;

   SRC_RDY_N <= "110";  -- Interface 0, valid frame, 1 part
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOF_N <= "110";
   EOP_N <= "110";      -- EOF, EOP
   wait for clkper;
   EOF_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   wait for 2*clkper;   -- Interface 0, valid frame, 2 parts
   SRC_RDY_N <= "110";
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";
   EOP_N <= "110";      -- EOP
   wait for clkper;
   EOP_N <= "111";
   SOP_N <= "110";      -- SOP
   wait for clkper;
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOF_N <= "110";
   EOP_N <= "110";      -- EOF, EOP
   wait for clkper;
   EOF_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   wait for 5*clkper;

   MI_RD <= '1';
   MI_ADDR <= X"00000008"; -- counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000010"; -- counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000018"; -- counter interface 2, result 0
   wait for clkper;
   MI_ADDR <= X"00000020"; -- invalid counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000028"; -- invalid counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000030"; -- invalid counter interface 2, result 0
   wait for clkper;
   MI_RD <= '0';

   MI_WR <= '1';           -- SEL <= '1', SAM <= '1'
   MI_ADDR <= X"00000000";
   MI_BE <= "0001";
   MI_DWR <= X"0000000D";
   wait for clkper;
   MI_WR <= '0';

   wait for 2*clkper;   -- Interface 0, valid frame, 3 parts
   SRC_RDY_N <= "110";
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";
   EOP_N <= "110";      -- EOP
   wait for clkper;
   EOP_N <= "111";
   SOP_N <= "110";      -- SOP
   wait for clkper;
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOP_N <= "110";      -- EOP
   wait for clkper;
   EOF_N <= "110";
   SOP_N <= "110";
   EOP_N <= "110";      -- EOF, SOP, EOP
   wait for clkper;
   EOF_N <= "111";
   SOP_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   wait for 5*clkper;

   MI_RD <= '1';
   MI_ADDR <= X"00000008"; -- counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000010"; -- counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000018"; -- counter interface 2, result 0
   wait for clkper;
   MI_ADDR <= X"00000020"; -- invalid counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000028"; -- invalid counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000030"; -- invalid counter interface 2, result 0
   wait for clkper;
   MI_RD <= '0';

   MI_WR <= '1';           -- SAM <= '1'
   MI_ADDR <= X"00000000";
   MI_BE <= "0001";
   MI_DWR <= X"0000000D";
   wait for clkper;
   MI_WR <= '0';

   MI_RD <= '1';
   MI_ADDR <= X"00000008"; -- counter interface 0, result 3
   wait for clkper;
   MI_ADDR <= X"00000010"; -- counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000018"; -- counter interface 2, result 0
   wait for clkper;
   MI_ADDR <= X"00000020"; -- invalid counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000028"; -- invalid counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000030"; -- invalid counter interface 2, result 0
   wait for clkper;
   MI_ADDR <= X"00000000"; -- control register, result 0x15
   wait for clkper;
   MI_RD <= '0';

   MI_WR <= '1';           -- SEL <= '0'
   MI_ADDR <= X"00000000";
   MI_BE <= "0001";
   MI_DWR <= X"00000001";
   wait for clkper;
   MI_WR <= '0';

   wait for 2*clkper;   -- Interface 2, invalid frame-2 cycles of SOF
   SRC_RDY_N <= "011";
   DST_RDY_N <= "011";
   SOF_N <= "011";
   SOP_N <= "011";      -- SOF, SOP
   wait for 2*clkper;
   SOF_N <= "111";
   SOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";
   wait for 5*clkper;

   wait for 2*clkper;   -- Interface 0, invalid frame-one EOP forgotten
   SRC_RDY_N <= "110";
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";
--   EOP_N <= "110";      -- EOP -- forgotten
   wait for clkper;
   EOP_N <= "111";
   SOP_N <= "110";      -- SOP
   wait for clkper;
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOP_N <= "110";      -- EOP
   wait for clkper;
   EOF_N <= "110";
   SOP_N <= "110";
   EOP_N <= "110";      -- EOF, SOP, EOP
   wait for clkper;
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   wait for 5*clkper;

   SRC_RDY_N <= "110";  -- Interface 0, valid frame, 1 part
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOF_N <= "110";
   EOP_N <= "110";      -- EOF, EOP
   wait for clkper;
   EOF_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   SRC_RDY_N <= "110";  -- Interface 0, valid frame, 1 part
   DST_RDY_N <= "110";
   SOF_N <= "110";
   SOP_N <= "110";      -- SOF, SOP
   wait for clkper;
   SOF_N <= "111";
   SOP_N <= "111";      -- data
   wait for 3*clkper;
   EOF_N <= "110";
   EOP_N <= "110";      -- EOF, EOP
   wait for clkper;
   EOF_N <= "111";
   EOP_N <= "111";
   SRC_RDY_N <= "111";
   DST_RDY_N <= "111";

   -- test RDY signals reading
   wait for 10*clkper;
   MI_RD <= '1';
   MI_ADDR <= X"00000038";
   wait for clkper;
   MI_RD <= '0';

   wait for clkper;

   SRC_RDY_N <= "101";
   DST_RDY_N <= "110";
   wait for clkper;
   MI_RD <= '1';
   wait for clkper;
   MI_RD <= '0';

   wait for 10*clkper;
   MI_RD <= '1';
   MI_ADDR <= X"00000008";
   wait for clkper;
   MI_RD <= '0';

   wait for 5*clkper;
   MI_ADDR <= X"00000000";
   MI_DWR(3 downto 0) <= "1101";
   -- MI_DWR(3) <= '1';
   MI_BE(0) <= '1';
   MI_WR <= '1';
   wait for clkper;
   MI_WR <= '0';
   MI_RD <= '1';
   wait for clkper;
   MI_ADDR <= X"00000008";
   wait for clkper;
   MI_RD <= '0';
   MI_DWR(3) <= '0';
   MI_WR <= '1';
   wait for clkper;
   MI_WR <= '0';

   wait for 10*clkper;
   MI_WR <= '1';
   MI_ADDR <= X"00000000"; -- reset counters
   MI_DWR <= X"00000003";
   wait for clkper;
   MI_WR <= '0';

   wait for 5*clkper;
   MI_RD <= '1';
   MI_ADDR <= X"00000008"; -- counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000010"; -- counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000018"; -- counter interface 2, result 0
   wait for clkper;
   MI_ADDR <= X"00000020"; -- invalid counter interface 0, result 2
   wait for clkper;
   MI_ADDR <= X"00000028"; -- invalid counter interface 1, result 1
   wait for clkper;
   MI_ADDR <= X"00000030"; -- invalid counter interface 2, result 0
   wait for clkper;
   MI_RD <= '0';

   wait;
end process;

end;
