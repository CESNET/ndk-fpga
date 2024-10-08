-- asfifo_dma_bus_ent.vhd : Entity of asynchronous FIFO for DMA bus
--!
--! \file
--! \brief Entity of asynchronous FIFO for DMA bus
--! \author Jiri Matousek <xmatou06@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity asfifo_dma_bus is
generic (
   --! \brief Width of DMA data
   DATA_WIDTH     : integer := 512;
   --! \brief Width of DMA header
   HDR_WIDTH      : integer := 96;
   --! \brief Use almost-full signal insted of full for DST_RDY
   USE_ALMOST_FULL: boolean := false;
   --! \brief Generic almost-full threshold. Valid range is 4-504 for Virtex 7
   ALMOST_FULL_OFFSET : integer := 4;

   ITEMS          : integer := 512;

   FAST_EMPTY     : boolean := true;

   FAST_EMPTY_DEPTH  : integer := 2;

   DEVICE         : string := "7SERIES"
);
port (
   --! \name Write interface
   -- -------------------------------------------------------------------------
   --! \brief Write clock
   WR_CLK         : in  std_logic;
   --! \brief Write reset
   WR_RESET       : in  std_logic;
   --! \brief DMA transaction data
   WR_DMA_DATA    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
   --! \brief DMA transaction header
   --! \details Valid when WR_DMA_SOP is valid.
   WR_DMA_HDR     : in  std_logic_vector(HDR_WIDTH-1 downto 0);
   --! \brief Start of DMA transaction
   --! \details Valid when WR_DMA_SRC_RDY = WR_DMA_DST_RDY = '1'.
   WR_DMA_SOP     : in  std_logic;
   --! \brief End of DMA transaction
   --! \details Valid when WR_DMA_SRC_RDY = WR_DMA_DST_RDY = '1'.
   WR_DMA_EOP     : in  std_logic;
   --! \brief Source is ready to transmit DMA data
   WR_DMA_SRC_RDY : in  std_logic;
   --! \brief Destination is ready to receive DMA data
   WR_DMA_DST_RDY : out std_logic;

   --! \name Read interface
   -- -------------------------------------------------------------------------
   --! \brief Read clock
   RD_CLK         : in  std_logic;
   --! \brief Read reset
   RD_RESET       : in  std_logic;
   --! \brief DMA transaction data
   RD_DMA_DATA    : out std_logic_vector(DATA_WIDTH-1 downto 0);
   --! \brief DMA transaction header
   --! \details Valid when RD_DMA_SOP is valid.
   RD_DMA_HDR     : out std_logic_vector(HDR_WIDTH-1 downto 0);
   --! \brief Start of DMA transaction
   --! \details Valid when RD_DMA_SRC_RDY = RD_DMA_DST_RDY = '1'.
   RD_DMA_SOP     : out std_logic;
   --! \brief End of DMA transaction
   --! \details Valid when RD_DMA_SRC_RDY = RD_DMA_DST_RDY = '1'.
   RD_DMA_EOP     : out std_logic;
   --! \brief Source is ready to transmit DMA data
   RD_DMA_SRC_RDY : out std_logic;
   --! \brief Destination is ready to receive DMA data
   RD_DMA_DST_RDY : in  std_logic
);
end entity asfifo_dma_bus;
