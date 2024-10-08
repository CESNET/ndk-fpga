--! asfifo_lut.vhd: Frame Link Unaliged protocol generic ASFIFO_LUT
--! Copyright (C) 2014 CESNET
--! Author: Jakub Cabal <jakubcabal@gmail.com>
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

--! ----------------------------------------------------------------------------
--!                            Entity declaration
--! ----------------------------------------------------------------------------

entity FLU_ASFIFO_LUT is
   generic(
      --! Data width
      --! \brief Should be power of 2 and higher than 16
      DATA_WIDTH     : integer := 256;
      SOP_POS_WIDTH  : integer := 2;
      --! number of items in the FIFO
      ITEMS          : integer := 64;
      --! Width of STATUS signal available
      STATUS_WIDTH   : integer := 1
   );
   port(
      -----------------------------------------------------
      --! \name Clocking & Reset interface
      -----------------------------------------------------
      RX_CLK            : in  std_logic;
      RX_RESET          : in  std_logic;
      TX_CLK            : in  std_logic;
      TX_RESET          : in  std_logic;

      -----------------------------------------------------
      --! \name Frame Link Unaligned input interface
      -----------------------------------------------------
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;
      RX_STATUS     : out std_logic_vector(STATUS_WIDTH-1 downto 0);

      -----------------------------------------------------
      --! \name Frame Link Unaligned output interface
      -----------------------------------------------------
      TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP        : out std_logic;
      TX_EOP        : out std_logic;
      TX_SRC_RDY    : out std_logic;
      TX_DST_RDY    : in std_logic
   );
end entity FLU_ASFIFO_LUT;

architecture full of FLU_ASFIFO_LUT is

   --! Constants declaration
   constant JUICE_WIDTH   : integer := 2;  --! SOP+EOP
   constant EOP_POS_WIDTH : integer := log2(DATA_WIDTH/8);
   constant MEM_WIDTH : integer := DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH+JUICE_WIDTH;
                              --!  DATA       EOP_POS       SOP_POS       FLU_JUICE

   --! Signals declaration
   signal sig_full      : std_logic;   --! FIFO is full
   signal sig_empty     : std_logic;   --! FIFO is empty
   signal sig_status    : std_logic_vector(STATUS_WIDTH-1 downto 0); --! Free items
   signal sig_vld       : std_logic;   --! Data valid at the output of the fifo
   signal sig_tx_src_rdy: std_logic;
   signal sig_rd        : std_logic;   --! Read from FIFO
   signal sig_wr        : std_logic;   --! Write to FIFO
   signal sig_data_rd   : std_logic_vector(MEM_WIDTH-1 downto 0); --! data from FIFO
   signal sig_data_wr   : std_logic_vector(MEM_WIDTH-1 downto 0); --! data from FIFO

begin

   --! Read signal generation
   sig_rd      <= TX_DST_RDY;
   --! Write signal generation
   sig_wr      <= RX_SRC_RDY and not sig_full;

   --! Signal TX_SRC_RDY
   sig_tx_src_rdy <= sig_vld;

   --! Data to write
   sig_data_wr <= RX_SOP & RX_EOP & RX_SOP_POS & RX_EOP_POS & RX_DATA;

   DATA_ASFIFO_I:entity work.asfifo
    generic map(
      --! ITEMS = Numer of items in FIFO
      --! !!!!!!!!!!! Must be (2^n), n>=2 !!!!!!!!!!!!!!!!!!!!!!
      ITEMS          => ITEMS,

      --! Data Width
      DATA_WIDTH     => MEM_WIDTH,

      --! Width of status information of fifo fullness
      --! Note: 2**STATUS_WIDTH MUST BE!! less or equal
      --!       than ITEMS
      STATUS_WIDTH   => STATUS_WIDTH
   )
   port map(

      --! Write interface
      CLK_WR      => RX_CLK,
      RST_WR      => RX_RESET,
      WR          => sig_wr,
      DI          => sig_data_wr,
      FULL        => sig_full,
      STATUS      => sig_status,

      --! Read interface
      CLK_RD      => TX_CLK,
      RST_RD      => TX_RESET,
      RD          => sig_rd,
      DO          => sig_data_rd,
      EMPTY       => sig_empty
   );

   sig_vld <= NOT sig_empty;
   --------------------------------------------------------
   --! RX signal map
   --------------------------------------------------------
   RX_DST_RDY  <= not(sig_full or RX_RESET);
   RX_STATUS   <= sig_status;

   --------------------------------------------------------
   --! TX signal map
   --------------------------------------------------------
   TX_SRC_RDY  <= sig_tx_src_rdy;
   TX_DATA     <= sig_data_rd(DATA_WIDTH-1 downto 0);
   TX_EOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH-1 downto DATA_WIDTH);
   TX_SOP_POS  <= sig_data_rd(DATA_WIDTH+EOP_POS_WIDTH+SOP_POS_WIDTH-1 downto DATA_WIDTH+EOP_POS_WIDTH);
   TX_EOP      <= sig_data_rd(MEM_WIDTH-2);
   TX_SOP      <= sig_data_rd(MEM_WIDTH-1);

end architecture full;
