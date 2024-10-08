-- testbench8.vhd: 8 bit FL_FIFO testbench
-- Copyright (C) 2007 CESNET
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
-- library with t_flxx data types
use work.fl_pkg.all;


ENTITY testbench IS
END testbench;

ARCHITECTURE testbench OF testbench IS

component FL_FIFO_FL8 is
   generic(
      -- True => use BlockBAMs
      -- False => use SelectRAMs
      USE_BRAMS      : boolean;
      -- number of items in the FIFO
      ITEMS          : integer;
      -- Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer;
      -- Width of STATUS signal
      STATUS_WIDTH   : integer;
      -- Number of parts in each frame
      PARTS          : integer
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- write interface
      RX             : inout t_fl8;
      -- read interface
      TX             : inout t_fl8;
      -- FIFO state signals
      LSTBLK         : out std_logic;
      FULL           : out std_logic;
      EMPTY          : out std_logic;
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      FRAME_RDY      : out std_logic
   );
end component FL_FIFO_FL8;

-- simulation constants
constant CLKPER      : time      := 10 ns;

constant DATA_WIDTH  : integer   := 8;
constant USE_BRAMS   : boolean   := false;
constant ITEMS       : integer   := 32;
constant BLOCK_SIZE  : integer   := 4;
constant STATUS_WIDTH: integer   := 3;
constant PARTS       : integer   := 1;

signal RX            : t_fl8;
signal TX            : t_fl8;

-- signals from/to tested unit
signal CLK           : std_logic;
signal RESET         : std_logic;

signal RX_DATA       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal RX_SRC_RDY_N  : std_logic;
signal RX_DST_RDY_N  : std_logic;
signal RX_SOP_N      : std_logic;
signal RX_EOP_N      : std_logic;
signal RX_SOF_N      : std_logic;
signal RX_EOF_N      : std_logic;

signal TX_DATA       : std_logic_vector(DATA_WIDTH-1 downto 0);
signal TX_SRC_RDY_N  : std_logic;
signal TX_DST_RDY_N  : std_logic;
signal TX_SOP_N      : std_logic;
signal TX_EOP_N      : std_logic;
signal TX_SOF_N      : std_logic;
signal TX_EOF_N      : std_logic;

signal LSTBLK        : std_logic;
signal EMPTY         : std_logic;
signal FULL          : std_logic;
signal STATUS        : std_logic_vector(STATUS_WIDTH-1 downto 0);
signal FRAME_RDY     : std_logic;


begin

RX.DATA     <= RX_DATA;
RX.SRC_RDY_N<= RX_SRC_RDY_N;
RX_DST_RDY_N<= RX.DST_RDY_N;
RX.SOP_N    <= RX_SOP_N;
RX.EOP_N    <= RX_EOP_N;
RX.SOF_N    <= RX_SOF_N;
RX.EOF_N    <= RX_EOF_N;

TX_DATA     <= TX.DATA;
TX_SRC_RDY_N<= TX.SRC_RDY_N;
TX.DST_RDY_N<= TX_DST_RDY_N;
TX_SOP_N    <= TX.SOP_N;
TX_EOP_N    <= TX.EOP_N;
TX_SOF_N    <= TX.SOF_N;
TX_EOF_N    <= TX.EOF_N;

-- Unit under test
uut: FL_FIFO_FL8
generic map(
   USE_BRAMS   => USE_BRAMS,
   ITEMS       => ITEMS,
   BLOCK_SIZE  => BLOCK_SIZE,
   STATUS_WIDTH=> STATUS_WIDTH,
   PARTS       => PARTS
)
port map(
   CLK         => CLK,
   RESET       => RESET,

   RX          => RX,
   TX          => TX,

   LSTBLK      => LSTBLK,
   FULL        => FULL,
   EMPTY       => EMPTY,
   STATUS      => STATUS,
   FRAME_RDY   => FRAME_RDY
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
   RESET       <= '1';
   RX_DATA     <= (others => '0');
   RX_SRC_RDY_N  <= '1';
   RX_SOP_N      <= '1';
   RX_EOP_N      <= '1';
   RX_SOF_N      <= '1';
   RX_EOF_N      <= '1';
   TX_DST_RDY_N  <= '1';

   wait for 4*clkper;
   RESET <= '0';
   wait for 4*clkper;

   -- Send second frame, the shortest possible
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(10, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- SOF, SOP, EOP

   RX_DATA  <= conv_std_logic_vector(11, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- SOP, EOP

   RX_DATA  <= conv_std_logic_vector(12, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- EOF, SOP, EOP

   RX_EOF_N   <= '1';
   RX_SOP_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';
   wait for 5*clkper;

   -- Send first frame - with header and footer
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(1, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   wait for clkper;  -- SOF, SOP

   RX_DATA  <= conv_std_logic_vector(2, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(3, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP

   RX_EOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(4, RX_DATA'length);
   RX_SOP_N   <= '0';
   TX_DST_RDY_N  <= '0';
   wait for clkper; -- SOP

   RX_DATA  <= conv_std_logic_vector(5, RX_DATA'length);
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(6, RX_DATA'length);
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(7, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP

   RX_EOP_N   <= '1';
   RX_SOP_N   <= '0';
   RX_DATA  <= conv_std_logic_vector(8, RX_DATA'length);
   wait for clkper; -- SOP

   RX_SOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(9, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP, EOF

   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';

   wait for 4*clkper;

   -- Read that frame from FIFO
   TX_DST_RDY_N <= '1';


   wait for 15*clkper;

   TX_DST_RDY_N <= '1';

   -- Send second frame, the shortest possible
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(10, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- SOF, SOP, EOP

   RX_DATA  <= conv_std_logic_vector(11, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- SOP, EOP

   RX_DATA  <= conv_std_logic_vector(12, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_SOP_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;  -- EOF, SOP, EOP

   RX_SRC_RDY_N <= '1';
   wait for 2*clkper;
   RX_SRC_RDY_N <= '0';
   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';

   -- Send another frame - this time with delay states
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(15, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   wait for clkper;  -- SOF, SOP

   RX_DATA  <= conv_std_logic_vector(2, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(3, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP

   RX_EOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(4, RX_DATA'length);
   RX_SOP_N   <= '0';
   wait for clkper; -- SOP

   RX_DATA  <= conv_std_logic_vector(5, RX_DATA'length);
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(6, RX_DATA'length);
   wait for clkper;

   RX_SRC_RDY_N <= '1';
   wait for 5*clkper;
   RX_SRC_RDY_N <= '0';

   RX_DATA  <= conv_std_logic_vector(7, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP

   RX_EOP_N   <= '1';
   RX_SOP_N   <= '0';
   RX_DATA  <= conv_std_logic_vector(8, RX_DATA'length);
   wait for clkper; -- SOP

   RX_SOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(6, RX_DATA'length);
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(9, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP, EOF

   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';

   wait for 4*clkper;

   TX_DST_RDY_N <= '0';

   wait for 15*clkper;

   RX_DATA     <= (others => '0');
   RX_SRC_RDY_N  <= '1';
   RX_SOP_N      <= '1';
   RX_EOP_N      <= '1';
   RX_SOF_N      <= '1';
   RX_EOF_N      <= '1';
   TX_DST_RDY_N  <= '1';

   -- Reset and start with two-field frames
   RESET <= '1';
   wait for 5*clkper;
   RESET <= '0';
   wait for 5*clkper;


 -- Send first frame - with two fields only
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(1, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   TX_DST_RDY_N  <= '0';
   wait for clkper;  -- SOF, SOP

   RX_DATA  <= conv_std_logic_vector(2, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(3, RX_DATA'length);
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP

   RX_EOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(4, RX_DATA'length);
   RX_SOP_N   <= '0';
   wait for clkper; -- SOP

   RX_DATA  <= conv_std_logic_vector(5, RX_DATA'length);
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(6, RX_DATA'length);
   wait for clkper;

   RX_SOP_N   <= '1';
   RX_DATA  <= conv_std_logic_vector(9, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP, EOF

   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';

   wait for 10*clkper;

   RX_DATA     <= (others => '0');
   RX_SRC_RDY_N  <= '1';
   RX_SOP_N      <= '1';
   RX_EOP_N      <= '1';
   RX_SOF_N      <= '1';
   RX_EOF_N      <= '1';
   TX_DST_RDY_N  <= '1';

   -- Reset and start with one-field frames
   RESET <= '1';
   wait for 5*clkper;
   RESET <= '0';
   wait for 5*clkper;

   -- Send first frame - with one field only
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(1, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   wait for clkper;  -- SOF, SOP

   RX_DATA  <= conv_std_logic_vector(20, RX_DATA'length);
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(300, RX_DATA'length);
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(4000, RX_DATA'length);
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(500, RX_DATA'length);
   wait for clkper;

   RX_DATA  <= conv_std_logic_vector(9, RX_DATA'length);
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper; -- EOP, EOF

   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';
   TX_DST_RDY_N  <= '0';

   wait for 10*clkper;

   -- Send the shortest possible frame
   RX_SRC_RDY_N <= '0';
   RX_DATA  <= conv_std_logic_vector(1, RX_DATA'length);
   RX_SOF_N   <= '0';
   RX_SOP_N   <= '0';
   RX_EOF_N   <= '0';
   RX_EOP_N   <= '0';
   wait for clkper;
   RX_SOF_N   <= '1';
   RX_SOP_N   <= '1';
   RX_EOF_N   <= '1';
   RX_EOP_N   <= '1';
   RX_SRC_RDY_N <= '1';

wait;
end process;

end;
