-- fifo_ent.vhd
--! \file
--! \brief Frame Link protocol generic FIFO entity.
--! \author Viktor Pus <pus@liberouter.org>
--! \section License
--! Copyright (C) 2006 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!
--! $Id$
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--! library containing log2 function
use work.math_pack.all;

--! FrameLink synchronous FIFO
entity FL_FIFO is
   generic(
      --! \brief Data width
      --! \details Should be multiple of 16: only 16,32,64,128 supported
      DATA_WIDTH     : integer := 16;
      --! \brief Type of memory
      --! \details True => use BlockBAMs
      --! \details False => use SelectRAMs
      USE_BRAMS      : boolean := false;
      --! Number of items in the FIFO
      ITEMS          : integer := 64;
      --! Size of block (for LSTBLK signal)
      BLOCK_SIZE     : integer := 1;
      --! Width of STATUS signal available
      STATUS_WIDTH   : integer := 1;
      --! Number of parts in each frame
      PARTS          : integer := 1;
      -- Ouptut register
      OUTPUT_REG : boolean := true
   );
   port(
      --! Input clock
      CLK            : in  std_logic;
      --! Synchronous reset
      RESET          : in  std_logic;

      ----------------------------------------------------------------------
      --! \name Write interface
      ----------------------------------------------------------------------
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

      ----------------------------------------------------------------------
      --! \name Read interface
      ----------------------------------------------------------------------
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
      TX_EOF_N       : out std_logic;

      ----------------------------------------------------------------------
      --! \name FIFO state signals
      ----------------------------------------------------------------------
      --! Writing to the last free block (defined by BLOCK_SIZE)
      LSTBLK         : out std_logic;
      --! FIFO is full
      FULL           : out std_logic;
      --! FIFO is empty
      EMPTY          : out std_logic;
      --! Detailed information about FIFO usage
      STATUS         : out std_logic_vector(STATUS_WIDTH-1 downto 0);
      --! At least one complete frame is stored in the FIFO
      FRAME_RDY      : out std_logic
   );
end entity FL_FIFO;
