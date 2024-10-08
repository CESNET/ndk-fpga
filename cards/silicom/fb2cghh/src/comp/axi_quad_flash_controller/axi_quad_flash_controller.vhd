-- axi_quad_flash_controller.vhd: Connection between top module and AXI4-LITE-MI_BRIDGE
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- This component is connecting AXI Quad SPI IP core with bridge unit.
-- Input SPI_CLK has to be atleast 100 MHz, otherwise function error occurs.
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

      -- STARTUP I/O signals
      -- Configuration clock
      CFGCLK      : out std_logic;
      -- Configuration internal oscillator clock
      CFGMCLK     : out std_logic;
      -- End of startup
      EOS         : out std_logic;
      -- Program request to fabric output
      PREQ        : out std_logic
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
         
         -- STARTUP_IO_S
         cfgclk        : out std_logic;
         cfgmclk       : out std_logic;
         eos           : out std_logic;
         preq          : out std_logic;
         gsr           : in  std_logic;
         gts           : in  std_logic;
         keyclearb     : in  std_logic;
         usrcclkts     : in  std_logic;
         usrdoneo      : in  std_logic;
         usrdonets     : in  std_logic
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

   --Write Response Channel
   signal bresp_s      : std_logic_vector(1 downto 0);
   signal bvalid_s     : std_logic;
   signal bready_s     : std_logic;

   -- Read Address Channel
   signal araddr_s     : std_logic_vector(G_AXI_ADDR_WIDTH - 1 downto 0); 
   signal arvalid_s    : std_logic;   
   signal arready_s    : std_logic;   

   --Read Data Channel
   signal rdata_s      : std_logic_vector(G_AXI_DATA_WIDTH - 1 downto 0);
   signal rresp_s      : std_logic_vector(1 downto 0);
   signal rvalid_s     : std_logic;
   signal rready_s     : std_logic;
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
         cfgclk        => CFGCLK,
         cfgmclk       => CFGMCLK,
         eos           => EOS,
         gsr           => '0',
         gts           => '0',
         keyclearb     => '1',
         preq          => PREQ,
         usrdoneo      => '1',
         usrcclkts     => '0',
         usrdonets     => '0'
      );

end architecture;
