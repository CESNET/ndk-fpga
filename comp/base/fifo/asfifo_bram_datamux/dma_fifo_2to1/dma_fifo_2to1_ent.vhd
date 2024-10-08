-- dma_fifo_2to1_ent.vhd
--!
--! \file
--! \brief Asynchronous fifo mutiplex in BRAMs for Xilinx FPGAs
--! \author Ondrej Dujiček <xdujic02@stud.feec.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library work;
use work.dma_bus_pack.all;

--\name  Asfifo module
entity DMAFIFO_MUX_2TO1 is
   generic(
      DIRECTION               : string  := "UP"; -- "UP" / "DOWN"
      DMA_HDR_WIDTH           : integer := DMA_UPHDR_WIDTH;
      DEVICE                  : string  := "7SERIES";
      ALMOST_FULL_OFFSET      : integer := 128;
      ALMOST_EMPTY_OFFSET     : integer := 128;
      INPUT_DATA_WIDTH        : integer := 512;
      USE_ALMOST_FULL         : boolean := false;
      -- Setting this value to 'true' disables ports CLK_WR, RST_WR (no FIFO will be present)
      -- The logic in that case is not perfect, so the throughput is greately reduced in this setting.
      FAKE_FIFO               : boolean := false
   );
   port(
      --! Write interface, all signals synchronous to CLK_WR
      CLK_WR         : in  std_logic;
      RST_WR         : in  std_logic;
      RX_SRC_RDY     : in  std_logic;
      RX_DST_RDY     : out std_logic;
      RX_HDR         : in  std_logic_vector(DMA_HDR_WIDTH-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_DATA_WIDTH-1 downto 0);
      RX_EOP         : in  std_logic;
      RX_SOP         : in  std_logic;

      --! Read interface, all signals synchronous to CLK_RD
      CLK_RD         : in  std_logic;
      RST_RD         : in  std_logic;
      TX_DATA        : out std_logic_vector(INPUT_DATA_WIDTH/2-1 downto 0);
      TX_HDR         : out std_logic_vector(DMA_HDR_WIDTH-1 downto 0);
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in  std_logic;
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic
   );
end entity DMAFIFO_MUX_2TO1;
