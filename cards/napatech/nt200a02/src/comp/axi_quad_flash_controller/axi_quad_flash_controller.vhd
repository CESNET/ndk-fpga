-- axi_quad_flash_controller.vhd: Connection between top module and AXI4-LITE-MI_BRIDGE
-- Copyright (C) 2025 DynaNIC Semiconductors s.r.o.
-- Author(s): Jan Privara <privara@dyna-nic.com>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
library UNISIM;
use UNISIM.vcomponents.all;

-- This component is connecting AXI Quad SPI IP core with bridge unit.
-- Input SPI_CLK has to be at least 100 MHz, otherwise function error occurs.
-- CLK frequency must be faster then SPI_CLK to comply Product Guide demand.
-- External link to AXI Quad SPI Product Guide is following:
-- https://docs.xilinx.com/r/en-US/pg153-axi-quad-spi/AXI-Quad-SPI-v3.2-LogiCORE-IP-Product-Guide
entity AXI_QUAD_FLASH_CONTROLLER is
   generic(
      G_AXI_ADDR_WIDTH : integer := 7;
      G_MI_ADDR_WIDTH  : integer := 8;
      G_AXI_DATA_WIDTH : integer := 32
      );
   port (

      -- clock and reset
      CLK          : in std_logic;
      SPI_CLK      : in std_logic;
      RST          : in std_logic;

      -- MI32 protocol
      AXI_MI_ADDR : in  std_logic_vector(G_MI_ADDR_WIDTH - 1 downto 0);
      AXI_MI_DWR  : in  std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
      AXI_MI_WR   : in  std_logic;
      AXI_MI_RD   : in  std_logic;
      AXI_MI_BE   : in  std_logic_vector((G_AXI_DATA_WIDTH/8)-1 downto 0);
      AXI_MI_ARDY : out std_logic;
      AXI_MI_DRD  : out std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
      AXI_MI_DRDY : out std_logic;

      -- QSPI signals
      QSPI_CLK     : inout std_logic;
      QSPI_IO      : inout std_logic_vector(3 downto 0);
      QSPI_SS      : inout std_logic
   );

end entity;

architecture FULL of AXI_QUAD_FLASH_CONTROLLER is

   component axi_quad_spi_0 is
      port (
         -- AXI Quad SPI interface

         --This clock is used for the SPI interface.
         --When ext_spi_clk is too slow, it is advised to use FIFO depth 256. (Frequency ratio is in the range of 50 to 100.)
         --This clock should be double of the maximum SPI frequency intended at the SPI interface.
         ext_spi_clk   : in  std_logic;
         -- AXI clock is expected to be faster than ext_spi_clk.
         s_axi_aclk    : in  std_logic;
         -- Negative reset
         s_axi_aresetn : in  std_logic;
         -- AXI_LITE interface
         s_axi_awaddr  : in  std_logic_vector(6 downto 0);
         s_axi_awvalid : in  std_logic;
         s_axi_awready : out std_logic;
         s_axi_wdata   : in  std_logic_vector(31 downto 0);
         s_axi_wstrb   : in  std_logic_vector(3 downto 0);
         s_axi_wvalid  : in  std_logic;
         s_axi_wready  : out std_logic;
         s_axi_bresp   : out std_logic_vector(1 downto 0);
         s_axi_bvalid  : out std_logic;
         s_axi_bready  : in  std_logic;
         s_axi_araddr  : in  std_logic_vector(6 downto 0);
         s_axi_arvalid : in  std_logic;
         s_axi_arready : out std_logic;
         s_axi_rdata   : out std_logic_vector(31 downto 0);
         s_axi_rresp   : out std_logic_vector(1 downto 0);
         s_axi_rvalid  : out std_logic;
         s_axi_rready  : in  std_logic;

         -- SPI
         io0_i         : in  std_logic;
         io0_o         : out std_logic;
         io0_t         : out std_logic;
         io1_i         : in  std_logic;
         io1_o         : out std_logic;
         io1_t         : out std_logic;
         io2_i         : in  std_logic;
         io2_o         : out std_logic;
         io2_t         : out std_logic;
         io3_i         : in  std_logic;
         io3_o         : out std_logic;
         io3_t         : out std_logic;
         sck_i         : in  std_logic;
         sck_o         : out std_logic;
         sck_t         : out std_logic;
         ss_i          : in  std_logic_vector ( 0 to 0 );
         ss_o          : out std_logic_vector ( 0 to 0 );
         ss_t          : out std_logic;

         ip2intc_irpt  : out std_logic
         );
   end component;

   -- Signals
   -- Write Address Channel
   signal awaddr_s     : std_logic_vector(G_AXI_ADDR_WIDTH - 1 downto 0);
   signal awvalid_s    : std_logic;
   signal awready_s    : std_logic;

   -- Write Data Channel
   signal wdata_s      : std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
   signal wstrb_s      : std_logic_vector((G_AXI_DATA_WIDTH/8)-1 downto 0);
   signal wvalid_s     : std_logic;
   signal wready_s     : std_logic;

   -- Write Response Channel
   signal bresp_s      : std_logic_vector(1 downto 0);
   signal bvalid_s     : std_logic;
   signal bready_s     : std_logic;

   -- Read Address Channel
   signal araddr_s     : std_logic_vector(G_AXI_ADDR_WIDTH - 1 downto 0);
   signal arvalid_s    : std_logic;
   signal arready_s    : std_logic;

   -- Read Data Channel
   signal rdata_s      : std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
   signal rresp_s      : std_logic_vector(1 downto 0);
   signal rvalid_s     : std_logic;
   signal rready_s     : std_logic;

   -- QSPI
   signal io0_i        :  std_logic;
   signal io0_o        :  std_logic;
   signal io0_t        :  std_logic;
   signal io1_i        :  std_logic;
   signal io1_o        :  std_logic;
   signal io1_t        :  std_logic;
   signal io2_i        :  std_logic;
   signal io2_o        :  std_logic;
   signal io2_t        :  std_logic;
   signal io3_i        :  std_logic;
   signal io3_o        :  std_logic;
   signal io3_t        :  std_logic;
   signal sck_i        :  std_logic;
   signal sck_o        :  std_logic;
   signal sck_t        :  std_logic;
   signal ss_i         :  std_logic_vector ( 0 to 0 );
   signal ss_o         :  std_logic_vector ( 0 to 0 );
   signal ss_t         :  std_logic;
-------------------------------------------------------------------------------
begin

   axi_bridge_i : entity work.AXI4_LITE_MI_BRIDGE
      generic map(
         G_AXI_ADDR_WIDTH => G_AXI_ADDR_WIDTH,
         G_MI_ADDR_WIDTH  => G_MI_ADDR_WIDTH,
         G_AXI_DATA_WIDTH => G_AXI_DATA_WIDTH
      )
      port map (
         CLK         => CLK,
         RST         => RST,
         AWADDR      => awaddr_s,
         AWVALID     => awvalid_s,
         AWREADY     => awready_s,
         WDATA       => wdata_s,
         WSTRB       => wstrb_s,
         WVALID      => wvalid_s,
         WREADY      => wready_s,
         BRESP       => bresp_s,
         BVALID      => bvalid_s,
         BREADY      => bready_s,
         ARADDR      => araddr_s,
         ARVALID     => arvalid_s,
         ARREADY     => arready_s,
         RDATA       => rdata_s,
         RRESP       => rresp_s,
         RVALID      => rvalid_s,
         RREADY      => rready_s,
         AXI_MI_ADDR => AXI_MI_ADDR,
         AXI_MI_DWR  => AXI_MI_DWR,
         AXI_MI_WR   => AXI_MI_WR,
         AXI_MI_RD   => AXI_MI_RD,
         AXI_MI_BE   => AXI_MI_BE,
         AXI_MI_ARDY => AXI_MI_ARDY,
         AXI_MI_DRD  => AXI_MI_DRD,
         AXI_MI_DRDY => AXI_MI_DRDY
      );

   axi_quad_ctrl_i : axi_quad_spi_0
      port map (
         ext_spi_clk   => SPI_CLK,
         s_axi_aclk    => CLK,
         s_axi_aresetn => not RST,
         s_axi_awaddr  => awaddr_s,
         s_axi_awvalid => awvalid_s,
         s_axi_awready => awready_s,
         s_axi_wdata   => wdata_s,
         s_axi_wstrb   => wstrb_s,
         s_axi_wvalid  => wvalid_s,
         s_axi_wready  => wready_s,
         s_axi_bresp   => bresp_s,
         s_axi_bvalid  => bvalid_s,
         s_axi_bready  => bready_s,
         s_axi_araddr  => araddr_s,
         s_axi_arvalid => arvalid_s,
         s_axi_arready => arready_s,
         s_axi_rdata   => rdata_s,
         s_axi_rresp   => rresp_s,
         s_axi_rvalid  => rvalid_s,
         s_axi_rready  => rready_s,
         io0_i         => io0_i,
         io0_o         => io0_o,
         io0_t         => io0_t,
         io1_i         => io1_i,
         io1_o         => io1_o,
         io1_t         => io1_t,
         io2_i         => io2_i,
         io2_o         => io2_o,
         io2_t         => io2_t,
         io3_i         => io3_i,
         io3_o         => io3_o,
         io3_t         => io3_t,
         sck_i         => sck_i,
         sck_o         => sck_o,
         sck_t         => sck_t,
         ss_i          => ss_i,
         ss_o          => ss_o,
         ss_t          => ss_t,
         ip2intc_irpt  => open
      );

      iobuf_qspi_clk : IOBUF
      port map (
         O  => sck_i,
         I  => sck_o,
         IO => QSPI_CLK,
         T  => sck_t
      );

      iobuf_qspi_ss : IOBUF
      port map (
         O  => ss_i(0),
         I  => ss_o(0),
         IO => QSPI_SS,
         T  => ss_t
      );

      iobuf_qspi_d0 : IOBUF
      port map (
         O  => io0_i,
         I  => io0_o,
         IO => QSPI_IO(0),
         T  => io0_t
      );

      iobuf_qspi_d1 : IOBUF
      port map (
         O  => io1_i,
         I  => io1_o,
         IO => QSPI_IO(1),
         T  => io1_t
      );

      iobuf_qspi_d2 : IOBUF
      port map (
         O  => io2_i,
         I  => io2_o,
         IO => QSPI_IO(2),
         T  => io2_t
      );

      iobuf_qspi_d3 : IOBUF
      port map (
         O  => io3_i,
         I  => io3_o,
         IO => QSPI_IO(3),
         T  => io3_t
      );

end architecture;
