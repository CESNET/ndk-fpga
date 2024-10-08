-- mfb_fifox.vhd: Multi-Frame Bus wraapper of FIFOX
-- Copyright (C) 2018 CESNET
-- Author(s): Michal Szabo <xszabo11@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

-- -------------------------------------------------------------------------
--                             Description
-- -------------------------------------------------------------------------

-- This component implements the FIFO memory for the MFB interface using the FIFOX component.
-- For more information about the FIFOX component, see the :ref:`documentation<fifox>`
--
entity MFB_FIFOX is
   generic(
   -- =========================================================================
   -- MFB parameters
   --
   -- Frame size restrictions: none
   -- =========================================================================

      -- any possitive value
      REGIONS             : natural := 4;
      -- any possitive value
      REGION_SIZE         : natural := 8;
      -- any possitive value
      BLOCK_SIZE          : natural := 8;
      ITEM_WIDTH          : natural := 8;
      -- Metadata width
      META_WIDTH          : natural := 0;

      -- =========================================================================
      -- FIFO parameters
      -- =========================================================================

      -- FIFO depth, number of data words
      FIFO_DEPTH          : natural := 512;
      -- Select memory implementation. Options:
      --   - "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32),
      --   - "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32),
      --   - "URAM"  - effective when ITEMS*FIFO_WIDTH >= 288000 and FIFO_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+)),
      --   - "SHIFT" - effective when ITEMS <= 16,
      --   - "AUTO"  - effective implementation dependent on ITEMS and DEVICE.
      RAM_TYPE            : string  := "AUTO";
      -- Defines what architecture is FIFO implemented on Options:
      --   - "ULTRASCALE" (Xilinx)
      --   - "7SERIES"    (Xilinx)
      --   - "ARRIA10"    (Intel)
      --   - "STRATIX10"  (Intel)
      DEVICE              : string  := "ULTRASCALE";
      -- Determins how many data words left free when almost_full is triggered.
      -- (ITEMS - ALMOST_FULL_OFFSET)
      ALMOST_FULL_OFFSET  : natural := 1;
      -- Determins how many data words present when almost_empty is triggered.
      -- (0 + ALMOST_EMPTY_OFFSET)
      ALMOST_EMPTY_OFFSET : natural := 1

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
      RX_META     : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
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
      TX_META     : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
      TX_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
      TX_EOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
      TX_SOF      : out std_logic_vector(REGIONS-1 downto 0);
      TX_EOF      : out std_logic_vector(REGIONS-1 downto 0);
      TX_SRC_RDY  : out std_logic;
      TX_DST_RDY  : in  std_logic;

      -- =========================================================================
      -- FIFO STATUS SIGNAL
      -- =========================================================================

      FIFO_STATUS : out std_logic_vector(log2(FIFO_DEPTH) downto 0);
      FIFO_AFULL  : out std_logic;
      FIFO_AEMPTY : out std_logic
   );
end MFB_FIFOX;

architecture behavioral of MFB_FIFOX is

   constant DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
   constant SOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
   constant EOF_POS_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));
   constant M_WIDTH       : natural := REGIONS*META_WIDTH;
   constant FIFO_WIDTH    : natural := DATA_WIDTH+M_WIDTH+SOF_POS_WIDTH+EOF_POS_WIDTH+REGIONS+REGIONS;

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
   s_fifo_din  <= RX_DATA & RX_META & RX_SOF_POS & RX_EOF_POS & RX_SOF & RX_EOF;
   s_fifo_wr   <= RX_SRC_RDY;
   RX_DST_RDY  <= not s_fifo_full;
   FIFO_STATUS <= s_fifo_status;

   -- FIFO instantiation
   -----------------------------------------------------------------------------
   fifo_i: entity work.fifox
   generic map(
      DATA_WIDTH          => FIFO_WIDTH,
      ITEMS               => FIFO_DEPTH,
      RAM_TYPE            => RAM_TYPE,
      DEVICE              => DEVICE,
      ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
      ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK         => CLK,
      RESET       => RST,
      -- Write interface
      DI          => s_fifo_din,
      WR          => s_fifo_wr,
      FULL        => s_fifo_full,
      AFULL       => FIFO_AFULL,
      STATUS      => s_fifo_status,
      -- Read interface
      DO          => s_fifo_dout,
      RD          => s_fifo_rd,
      EMPTY       => s_fifo_vld,
      AEMPTY      => FIFO_AEMPTY
   );

   -- Connection read interface of FIFO
   -----------------------------------------------------------------------------
   TX_EOF     <= s_fifo_dout(  REGIONS                                    -1 downto                                     0);
   TX_SOF     <= s_fifo_dout(2*REGIONS                                    -1 downto   REGIONS                            );
   TX_EOF_POS <= s_fifo_dout(2*REGIONS+EOF_POS_WIDTH                      -1 downto 2*REGIONS                            );
   TX_SOF_POS <= s_fifo_dout(2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH        -1 downto 2*REGIONS+EOF_POS_WIDTH              );
   TX_META    <= s_fifo_dout(2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH+M_WIDTH-1 downto 2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH);
   TX_DATA    <= s_fifo_dout(FIFO_WIDTH-1 downto 2*REGIONS+EOF_POS_WIDTH+SOF_POS_WIDTH+M_WIDTH);
   TX_SRC_RDY <= not s_fifo_vld;
   s_fifo_rd  <= TX_DST_RDY;

end architecture;
