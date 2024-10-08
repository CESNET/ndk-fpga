-- mfb_fifo_bram.vhd: Multi-Frame Bus wrapper of FIFO implemented in behavioral BRAMs
-- Copyright (C) 2017 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity MFB_FIFO_BRAM is
   generic(
      -- =========================================================================
      -- BUS GENERIC
      --
      -- Frame size restrictions: none
      -- =========================================================================

      -- any possitive value
      REGIONS     : natural := 4;
      -- any possitive value
      REGION_SIZE : natural := 8;
      -- any possitive value
      BLOCK_SIZE  : natural := 8;
      -- any possitive value
      ITEM_WIDTH  : natural := 8;
      -- 512, 1024, 2048, 4096,...
      FIFO_DEPTH  : natural := 512
   );
   port(
      -- =========================================================================
      -- CLOCK AND RESET
      -- =========================================================================

      CLK         : in  std_logic;
      RST         : in  std_logic;

      -- =========================================================================
      -- RX MFB INTERFACE
      -- =========================================================================

      RX_DATA     : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      RX_SOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      RX_EOF_POS  : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      RX_SOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_EOF      : in  std_logic_vector(REGIONS-1 downto 0);
      RX_SRC_RDY  : in  std_logic;
      RX_DST_RDY  : out std_logic;

      -- =========================================================================
      -- TX MFB INTERFACE
      -- =========================================================================

      TX_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
      TX_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF      : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF      : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY  : out std_logic;
      TX_DST_RDY  : in  std_logic;

      -- =========================================================================
      -- FIFO STATUS SIGNAL
      -- =========================================================================

      FIFO_STATUS : out std_logic_vector(log2(FIFO_DEPTH) downto 0)
   );
end MFB_FIFO_BRAM;

architecture behavioral of MFB_FIFO_BRAM is

   constant DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant FIFO_WIDTH    : natural := DATA_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS;

   signal s_fifo_din      : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal s_fifo_wr       : std_logic;
   signal s_fifo_full     : std_logic;
   signal s_fifo_status   : std_logic_vector(log2(FIFO_DEPTH) downto 0);

   signal s_fifo_dout     : std_logic_vector(FIFO_WIDTH-1 downto 0);
   signal s_fifo_rd       : std_logic;
   signal s_fifo_vld      : std_logic;

begin

   -- Connection write interface of FIFO
   -----------------------------------------------------------------------------
   s_fifo_din  <= RX_DATA & RX_SOF_POS & RX_EOF_POS & RX_SOF & RX_EOF;
   s_fifo_wr   <= RX_SRC_RDY;
   RX_DST_RDY  <= not s_fifo_full;
   FIFO_STATUS <= s_fifo_status;

   -- FIFO instantiation
   -----------------------------------------------------------------------------
   fifo_i: entity work.FIFO_BRAM
   generic map(
      STATUS_ENABLED => True,
      ITEMS          => FIFO_DEPTH,
      BLOCK_SIZE     => 0,
      DATA_WIDTH     => FIFO_WIDTH,
      DO_REG         => True,
      AUTO_PIPELINE  => True
   )
   port map(
      RESET       => RST,
      CLK         => CLK,
      -- Write interface
      DI          => s_fifo_din,
      WR          => s_fifo_wr,
      FULL        => s_fifo_full,
      LSTBLK      => open,
      STATUS      => s_fifo_status,
      -- Read interface
      DO          => s_fifo_dout,
      RD          => s_fifo_rd,
      EMPTY       => open,
      DV          => s_fifo_vld
   );

   -- Connection read interface of FIFO
   -----------------------------------------------------------------------------
   TX_EOF     <= s_fifo_dout(REGIONS-1 downto 0);
   TX_SOF     <= s_fifo_dout(2*REGIONS-1 downto REGIONS);
   TX_EOF_POS <= s_fifo_dout(2*REGIONS+EOF_POS_WIDTH-1 downto 2*REGIONS);
   TX_SOF_POS <= s_fifo_dout(2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH-1 downto 2*REGIONS+EOF_POS_WIDTH);
   TX_DATA    <= s_fifo_dout(FIFO_WIDTH-1 downto 2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH);
   TX_SRC_RDY <= s_fifo_vld;
   s_fifo_rd  <= TX_DST_RDY;

end architecture;
