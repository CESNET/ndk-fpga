-- dmafifo_1to2_ent.vhd
--!
--! \file
--! \brief Asynchronous fifo mutiplex in BRAMs for Xilinx FPGAs
--! \author Ondrej Dujiček <xdujic02@stud.feec.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

--\name  Asfifo module
entity DMAFIFO_MUX_1TO2 is
   generic(
      DEVICE                         : string := "7SERIES";
      ALMOST_FULL_OFFSET             : integer := 128;
      ALMOST_EMPTY_OFFSET            : integer := 128;
      HDR_WIDTH                      : integer := 32;
      INPUT_DATA_WIDTH               : integer := 256;
      --! Do not check internally RX_DST_RDY.
      --! When enabled, user may not set RX_SRC_RDY when RX_DST_RDY is in 0.
      --! This is a logic opt for use with AFULL.
      DISABLE_DST_RDY                : boolean := false
   );
   port (
      --! Write interface, all signals synchronous to CLK_WR
      CLK_WR         : in  std_logic;
      RST_WR         : in  std_logic;
      RX_EOP         : in  std_logic;
      RX_SOP         : in  std_logic;
      RX_HDR         : in  std_logic_vector (HDR_WIDTH-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
      RX_SRC_RDY     : in  std_logic;
      RX_DST_RDY     : out std_logic;
      RX_AFULL       : out std_logic;

      --! Read interface, all signals synchronous to CLK_RD
      CLK_RD         : in  std_logic;
      RST_RD         : in  std_logic;
      TX_DATA        : out std_logic_vector(INPUT_DATA_WIDTH*2-1  downto 0);
      TX_HDR         : out std_logic_vector(HDR_WIDTH - 1 downto 0);
      TX_EOP         : out std_logic;
      TX_SOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in  std_logic;
      TX_SRC_RDY_H   : out std_logic   --! If upper part of world is also valid
   );
end entity DMAFIFO_MUX_1TO2;
