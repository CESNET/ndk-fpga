-- fl_asfifo_lut.vhd
--!
--! \file
--! \brief Async FL_FIFO composed of FPGA built-in FIFOs.
--! \author Jakub Cabal <jakubcabal@gmail.com>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Package with log2 function.
use work.math_pack.all;

--! \brief Generic async FL_FIFO composed of FPGA built-in FIFOs.
entity FL_ASFIFO_LUT is
  generic (
    --! \brief Data width of input and output FrameLink data.
    --! \details Must be greater than 8.
    DATA_WIDTH     : integer := 128;
    --! \brief Number of items in the FIFO.
    ITEMS          : integer := 128
  );
  port (
    --! \name Resets and clocks

    --! Input Framelink clock
    RX_CLK         : in  std_logic;
    --! Input Framelink reset
    RX_RESET       : in  std_logic;
    --! Output Framelink clock
    TX_CLK         : in  std_logic;
    --! Output Framelink reset
    TX_RESET       : in  std_logic;

    --! \name Write interface

    --! Write side data
    RX_DATA        : in  std_logic_vector(DATA_WIDTH-1 downto 0);
    --! Write side data remainder
    RX_REM         : in  std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    --! Write side not source ready
    RX_SRC_RDY_N   : in  std_logic;
    --! Write side not destination ready
    RX_DST_RDY_N   : out std_logic;
    --! Write side not start of part
    RX_SOP_N       : in  std_logic;
    --! Write side not end of part
    RX_EOP_N       : in  std_logic;
    --! Write side not start of frame
    RX_SOF_N       : in  std_logic;
    --! Write side not end of frame
    RX_EOF_N       : in  std_logic;

    --! \name Read interface

    --! Read side data
    TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
    --! Read side data remainder
    TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8) - 1 downto 0);
    --! Read side not source ready
    TX_SRC_RDY_N   : out std_logic;
    --! Read side not destination ready
    TX_DST_RDY_N   : in  std_logic;
    --! Read side not start of part
    TX_SOP_N       : out std_logic;
    --! Read side not end of part
    TX_EOP_N       : out std_logic;
    --! Read side not start of frame
    TX_SOF_N       : out std_logic;
    --! Read side not end of frame
    TX_EOF_N       : out std_logic
  );
end entity;

--! \brief Full implementation of async FL_FIFO composed of FPGA built-in FIFOs.
architecture full of FL_ASFIFO_LUT is
  constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
  constant FIFO_WIDTH    : integer := DATA_WIDTH+EOP_POS_WIDTH+1+1+1+1;

  signal full            : std_logic;
  signal empty           : std_logic;
  signal read            : std_logic;
  signal write           : std_logic;
  signal data_in         : std_logic_vector(FIFO_WIDTH-1 downto 0);
  signal data_out        : std_logic_vector(FIFO_WIDTH-1 downto 0);
begin
  --! data path connection
  data_in      <= RX_DATA & RX_REM & RX_SOP_N & RX_EOP_N & RX_SOF_N & RX_EOF_N;
  TX_DATA      <= data_out(FIFO_WIDTH-1 downto FIFO_WIDTH-DATA_WIDTH);
  TX_REM       <= data_out(EOP_POS_WIDTH+3 downto 4);
  TX_SOP_N     <= data_out(3);
  TX_EOP_N     <= data_out(2);
  TX_SOF_N     <= data_out(1);
  TX_EOF_N     <= data_out(0);

  --! input control
  RX_DST_RDY_N <= full;
  write        <= not RX_SRC_RDY_N and not full;

  --! ASFIFO
  asfifo : entity work.ASFIFO
    generic map (
      DATA_WIDTH   => FIFO_WIDTH,
      --! Item in memory needed, one item size is DATA_WIDTH
      ITEMS        => ITEMS,
      STATUS_WIDTH => 1 --! Ignore
    ) port map (
      CLK_WR   => RX_CLK,
      RST_WR   => RX_RESET,
      DI       => data_in,
      WR       => write,
      STATUS   => open,
      FULL     => full,
      CLK_RD   => TX_CLK,
      RST_RD   => TX_RESET,
      DO       => data_out,
      RD       => read,
      EMPTY    => empty
    );

  --! output control
  TX_SRC_RDY_N <= empty;
  read         <= not TX_DST_RDY_N and not empty;

end architecture full;
