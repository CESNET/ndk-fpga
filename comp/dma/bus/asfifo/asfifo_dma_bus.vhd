-- asfifo_dma_bus.vhd : Architecture of asynchronous FIFO for DMA bus
--!
--! \file
--! \brief Architecture of asynchronous FIFO for DMA bus
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


-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

architecture full of asfifo_dma_bus is

   --! Constants declaration
   -- -------------------------------------------------------------------------

   constant INTERNAL_DATA_WIDTH : integer := DATA_WIDTH + HDR_WIDTH + 2;

   --! Signals declaration
   -- -------------------------------------------------------------------------

   --! write interface
   signal wr_data   : std_logic_vector(INTERNAL_DATA_WIDTH-1 downto 0);
   signal wr_enable : std_logic;
   signal full      : std_logic;
   signal afull_sig : std_logic;
   signal full_sig  : std_logic;

   --! read interface
   signal rd_data   : std_logic_vector(INTERNAL_DATA_WIDTH-1 downto 0);
   signal rd_enable : std_logic;
   signal empty     : std_logic;


-- ----------------------------------------------------------------------------
--                            Architecture body
-- ----------------------------------------------------------------------------

begin

   --! aggregation of input port to write data signal
   wr_data        <= WR_DMA_EOP & WR_DMA_SOP & WR_DMA_HDR & WR_DMA_DATA;

   --! wite interface logic
   wr_enable      <= WR_DMA_SRC_RDY AND NOT full;
   WR_DMA_DST_RDY <= NOT full;
   --! select desired full signal along to generic
   full           <= afull_sig when USE_ALMOST_FULL = true else full_sig;

   --! DMA asynchronous FIFO for downstream
   asfifo_dma_bus_i : entity work.ASFIFO_BRAM_XILINX
   generic map (
      DEVICE              => DEVICE,
      DATA_WIDTH          => INTERNAL_DATA_WIDTH,
      ITEMS               => ITEMS,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
      PRECISE_FULL            => false,
      FAST_EMPTY              => FAST_EMPTY,
      FAST_EMPTY_DEPTH        => FAST_EMPTY_DEPTH
   )
   port map (
      --! Write interface
      CLK_WR              => WR_CLK,
      RST_WR              => WR_RESET,
      DI                  => wr_data,
      WR                  => wr_enable,
      AFULL               => afull_sig,
      FULL                => full_sig,

      --! Read interface
      CLK_RD              => RD_CLK,
      RST_RD              => RD_RESET,
      DO                  => rd_data,
      RD                  => rd_enable,
      AEMPTY              => open,
      EMPTY               => empty
   );

   --! de-aggregation of read data signal to output ports
   RD_DMA_DATA <= rd_data(DATA_WIDTH-1 downto 0);
   RD_DMA_HDR  <= rd_data(INTERNAL_DATA_WIDTH-3 downto DATA_WIDTH);
   RD_DMA_SOP  <= rd_data(INTERNAL_DATA_WIDTH-2);
   RD_DMA_EOP  <= rd_data(INTERNAL_DATA_WIDTH-1);

   --! read interface logic
   rd_enable      <= RD_DMA_DST_RDY AND NOT empty;
   RD_DMA_SRC_RDY <= NOT empty;

end architecture full;
