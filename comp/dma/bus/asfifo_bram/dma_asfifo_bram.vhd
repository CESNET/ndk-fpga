--! dma_asfifo_bram.vhd : Entity of asynchronous FIFO for DMA bus
--!
--! \file
--! \brief Entity of asynchronous FIFO for DMA bus
--! \author Jakub Cabal <jakubcabal@gmail.com>
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

use work.math_pack.all;
use work.type_pack.all;

entity DMA_ASFIFO_BRAM is
generic (
   --! \brief Width of DMA data
   DATA_WIDTH       : integer := 512;
   --! \brief Width of DMA header
   HDR_WIDTH        : integer := 96;
   --! \brief number of items
   ITEMS            : integer := 512;
   -- additional status signal width (default must be 0, other option 1 to express status on log2(ITEMS+1) bits)
   STATUS_ADD_WIDTH : integer := 0
);
port (
   --! \name Write interface
   --! -------------------------------------------------------------------------
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

   --! \brief Status signal
   WR_STATUS      : out std_logic_vector(log2(ITEMS+STATUS_ADD_WIDTH)-1 downto 0);


   --! \name Read interface
   --! -------------------------------------------------------------------------
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
end entity DMA_ASFIFO_BRAM;

--! ----------------------------------------------------------------------------
--!                        Architecture declaration
--! ----------------------------------------------------------------------------

architecture full of DMA_ASFIFO_BRAM is

   --! Constants declaration
   --! -------------------------------------------------------------------------

   constant INTERNAL_DATA_WIDTH : integer := DATA_WIDTH + HDR_WIDTH + 2;

   --! Signals declaration
   --! -------------------------------------------------------------------------

   --! write interface
   signal wr_data   : std_logic_vector(INTERNAL_DATA_WIDTH-1 downto 0);
   signal wr_enable : std_logic;
   signal full      : std_logic;

   --! read interface
   signal rd_data   : std_logic_vector(INTERNAL_DATA_WIDTH-1 downto 0);
   signal rd_enable : std_logic;
   signal do_vd     : std_logic;

--! ----------------------------------------------------------------------------
--!                            Architecture body
--! ----------------------------------------------------------------------------

begin

   --! aggregation of input port to write data signal
   wr_data        <= WR_DMA_EOP & WR_DMA_SOP & WR_DMA_HDR & WR_DMA_DATA;

   --! wite interface logic
   wr_enable      <= WR_DMA_SRC_RDY AND NOT full;
   WR_DMA_DST_RDY <= NOT full;

   --! DMA asynchronous FIFO for downstream
   asfifo_dma_bus_i : entity work.ASFIFO_BRAM
   generic map (
      DATA_WIDTH    => INTERNAL_DATA_WIDTH,
      --! Item in memory needed, one item size is DATA_WIDTH
      ITEMS            => ITEMS,
      AUTO_PIPELINE    => true,
      STATUS_WIDTH     => log2(ITEMS+STATUS_ADD_WIDTH),
      STATUS_ADD_WIDTH => STATUS_ADD_WIDTH
   )
   port map (
      --! Write interface
      CLK_WR              => WR_CLK,
      RST_WR              => WR_RESET,
      DI                  => wr_data,
      WR                  => wr_enable,
      STATUS              => WR_STATUS,
      FULL                => full,

      --! Read interface
      CLK_RD              => RD_CLK,
      RST_RD              => RD_RESET,
      DO                  => rd_data,
      RD                  => rd_enable,
      DO_DV               => do_vd,
      EMPTY               => open
   );

   --! de-aggregation of read data signal to output ports
   RD_DMA_DATA <= rd_data(DATA_WIDTH-1 downto 0);
   RD_DMA_HDR  <= rd_data(INTERNAL_DATA_WIDTH-3 downto DATA_WIDTH);
   RD_DMA_SOP  <= rd_data(INTERNAL_DATA_WIDTH-2);
   RD_DMA_EOP  <= rd_data(INTERNAL_DATA_WIDTH-1);

   --! read interface logic
   rd_enable      <= RD_DMA_DST_RDY AND do_vd;
   RD_DMA_SRC_RDY <= do_vd;

end architecture full;
