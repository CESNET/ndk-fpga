-- versal_ps_ctrl.vhd : Toplevel component for PS access on Versal chips.
--                      Provides FPGA ID and boot flash access and control.
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

-- Gives the FPGA design and the host software access to the Processing System (PS) of AMD Versal devices:
-- FPGA ID (device DNA), a 2 KB window into the PS address space and the BMC mailbox.
entity VERSAL_PS_CTRL is
    generic (
        -- AXI data word width in bits, must be 32
        AXI_DATA_WIDTH     : natural := 32;
        -- Address width in bits, depends on PS port to which is the component
        -- connected.
        -- E.g. Use 49 if accessing via Slave AXI LPD PS interface
        AXI_ADDR_WIDTH     : natural := 49;
        -- ID width, depends on PS port to which is the component connected.
        -- E.g. Use 6 if accessing via Slave AXI LPD PS interface
        AXI_ID_WIDTH       : natural := 6;
        -- ARUSER width, depends on PS port to which is the component connected.
        -- Used for System Management ID (SMID)
        -- E.g. Use 10 if accessing via Slave AXI LPD PS interface
        AXI_ARUSER_WIDTH   : natural := 10;
        -- AWUSER width, depends on PS port to which is the component connected.
        -- Used for System Management ID (SMID)
        -- E.g. Use 10 if accessing via Slave AXI LPD PS interface
        AXI_AWUSER_WIDTH   : natural := 10;
        -- Read/Write SMID. It's OK for them to be the same. SMID value must be
        -- unique in the PL design, it identifies the master. Note, that there
        -- are rules for its value. E.g. on Slave AXI LPD PS interface the
        -- highest bit must be zero to indicate PL master. See Versal
        -- documentation for details.
        READ_SMID          : std_logic_vector(AXI_ARUSER_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(1, AXI_ARUSER_WIDTH));
        WRITE_SMID         : std_logic_vector(AXI_AWUSER_WIDTH - 1 downto 0) := std_logic_vector(to_unsigned(1, AXI_AWUSER_WIDTH));

        -- Internal address width in bits 32 or 64
        -- Use 64 if accessing via NOC, 32 otherwise
        AXI_ADDR_WIDTH_INT : natural := 32;
        -- Target device
        DEVICE             : string  := "VERSAL"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        -- Clock of the MI interface and of the FPGA_ID interface
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- Clock of the AXI4-Lite interface from PS, of the AXI4 interface and of the internal logic
        AXI_LITE_CLK     : in std_logic;
        AXI_LITE_RESET   : in std_logic;

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR           : in  std_logic_vector(31 downto 0);
        MI_ADDR          : in  std_logic_vector(31 downto 0);
        MI_RD            : in  std_logic;
        MI_WR            : in  std_logic;
        MI_BE            : in  std_logic_vector(3 downto 0);
        MI_DRD           : out std_logic_vector(31 downto 0);
        MI_ARDY          : out std_logic;
        MI_DRDY          : out std_logic;

        -- =====================================================================
        -- AXI4-Lite interface from PS (slave)
        -- =====================================================================
        AXI_LITE_AWADDR  : in  std_logic_vector(31 downto 0);
        AXI_LITE_AWVALID : in  std_logic;
        AXI_LITE_AWREADY : out std_logic;

        AXI_LITE_WDATA   : in  std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
        AXI_LITE_WSTRB   : in  std_logic_vector(AXI_DATA_WIDTH / 8 - 1 downto 0);
        AXI_LITE_WVALID  : in  std_logic;
        AXI_LITE_WREADY  : out std_logic;

        AXI_LITE_BRESP   : out std_logic_vector(1 downto 0);
        AXI_LITE_BVALID  : out std_logic;
        AXI_LITE_BREADY  : in  std_logic;

        AXI_LITE_ARADDR  : in  std_logic_vector(31 downto 0);
        AXI_LITE_ARVALID : in  std_logic;
        AXI_LITE_ARREADY : out std_logic;

        AXI_LITE_RDATA   : out std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
        AXI_LITE_RRESP   : out std_logic_vector(1 downto 0);
        AXI_LITE_RVALID  : out std_logic;
        AXI_LITE_RREADY  : in  std_logic;

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID         : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_AWADDR       : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWUSER       : out std_logic_vector(AXI_AWUSER_WIDTH - 1 downto 0);
        AXI_AWLEN        : out std_logic_vector(8-1 downto 0);
        AXI_AWSIZE       : out std_logic_vector(3-1 downto 0);
        AXI_AWBURST      : out std_logic_vector(2-1 downto 0);
        AXI_AWPROT       : out std_logic_vector(3-1 downto 0);
        AXI_AWCACHE      : out std_logic_vector(4-1 downto 0);
        AXI_AWLOCK       : out std_logic;
        AXI_AWQOS        : out std_logic_vector(4-1 downto 0);
        AXI_AWVALID      : out std_logic;
        AXI_AWREADY      : in  std_logic;
        AXI_WDATA        : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB        : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_WLAST        : out std_logic;
        AXI_WVALID       : out std_logic;
        AXI_WREADY       : in  std_logic;
        AXI_BID          : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_BRESP        : in  std_logic_vector(2-1 downto 0);
        AXI_BVALID       : in  std_logic;
        AXI_BREADY       : out std_logic;
        AXI_ARID         : out std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_ARADDR       : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_ARUSER       : out std_logic_vector(AXI_ARUSER_WIDTH - 1 downto 0);
        AXI_ARLEN        : out std_logic_vector(8-1 downto 0);
        AXI_ARSIZE       : out std_logic_vector(3-1 downto 0);
        AXI_ARBURST      : out std_logic_vector(2-1 downto 0);
        AXI_ARPROT       : out std_logic_vector(3-1 downto 0);
        AXI_ARCACHE      : out std_logic_vector(4-1 downto 0);
        AXI_ARLOCK       : out std_logic;
        AXI_ARQOS        : out std_logic_vector(4-1 downto 0);
        AXI_ARVALID      : out std_logic;
        AXI_ARREADY      : in  std_logic;
        AXI_RID          : in  std_logic_vector(AXI_ID_WIDTH-1 downto 0);
        AXI_RDATA        : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_RRESP        : in  std_logic_vector(2-1 downto 0);
        AXI_RLAST        : in  std_logic;
        AXI_RVALID       : in  std_logic;
        AXI_RREADY       : out std_logic;

        -- =====================================================================
        -- FPGA_ID interface
        -- =====================================================================
        FPGA_ID          : out std_logic_vector(127 downto 0);
        FPGA_ID_VLD      : out std_logic
    );

end entity;

architecture FULL of VERSAL_PS_CTRL is
    signal fpga_id_int      : std_logic_vector(127 downto 0);
    signal fpga_id_int_vld  : std_logic;

    signal axi_id_awid      : std_logic_vector(8-1 downto 0);
    signal axi_id_awaddr    : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_id_awlen     : std_logic_vector(8-1 downto 0);
    signal axi_id_awsize    : std_logic_vector(3-1 downto 0);
    signal axi_id_awburst   : std_logic_vector(2-1 downto 0);
    signal axi_id_awprot    : std_logic_vector(3-1 downto 0);
    signal axi_id_awvalid   : std_logic;
    signal axi_id_awready   : std_logic;
    signal axi_id_wdata     : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_id_wstrb     : std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
    signal axi_id_wlast     : std_logic;
    signal axi_id_wvalid    : std_logic;
    signal axi_id_wready    : std_logic;
    signal axi_id_bid       : std_logic_vector(8-1 downto 0);
    signal axi_id_bresp     : std_logic_vector(2-1 downto 0);
    signal axi_id_bvalid    : std_logic;
    signal axi_id_bready    : std_logic;
    signal axi_id_arid      : std_logic_vector(8-1 downto 0);
    signal axi_id_araddr    : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_id_arlen     : std_logic_vector(8-1 downto 0);
    signal axi_id_arsize    : std_logic_vector(3-1 downto 0);
    signal axi_id_arburst   : std_logic_vector(2-1 downto 0);
    signal axi_id_arprot    : std_logic_vector(3-1 downto 0);
    signal axi_id_arvalid   : std_logic;
    signal axi_id_arready   : std_logic;
    signal axi_id_rid       : std_logic_vector(8-1 downto 0);
    signal axi_id_rdata     : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_id_rresp     : std_logic_vector(2-1 downto 0);
    signal axi_id_rlast     : std_logic;
    signal axi_id_rvalid    : std_logic;
    signal axi_id_rready    : std_logic;

    signal axi_boot_awid    : std_logic_vector(8-1 downto 0);
    signal axi_boot_awaddr  : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_boot_awlen   : std_logic_vector(8-1 downto 0);
    signal axi_boot_awsize  : std_logic_vector(3-1 downto 0);
    signal axi_boot_awburst : std_logic_vector(2-1 downto 0);
    signal axi_boot_awprot  : std_logic_vector(3-1 downto 0);
    signal axi_boot_awvalid : std_logic;
    signal axi_boot_awready : std_logic;
    signal axi_boot_wdata   : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_boot_wstrb   : std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
    signal axi_boot_wlast   : std_logic;
    signal axi_boot_wvalid  : std_logic;
    signal axi_boot_wready  : std_logic;
    signal axi_boot_bid     : std_logic_vector(8-1 downto 0);
    signal axi_boot_bresp   : std_logic_vector(2-1 downto 0);
    signal axi_boot_bvalid  : std_logic;
    signal axi_boot_bready  : std_logic;
    signal axi_boot_arid    : std_logic_vector(8-1 downto 0);
    signal axi_boot_araddr  : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_boot_arlen   : std_logic_vector(8-1 downto 0);
    signal axi_boot_arsize  : std_logic_vector(3-1 downto 0);
    signal axi_boot_arburst : std_logic_vector(2-1 downto 0);
    signal axi_boot_arprot  : std_logic_vector(3-1 downto 0);
    signal axi_boot_arvalid : std_logic;
    signal axi_boot_arready : std_logic;
    signal axi_boot_rid     : std_logic_vector(8-1 downto 0);
    signal axi_boot_rdata   : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_boot_rresp   : std_logic_vector(2-1 downto 0);
    signal axi_boot_rlast   : std_logic;
    signal axi_boot_rvalid  : std_logic;
    signal axi_boot_rready  : std_logic;

    signal axi_sw_awid      : std_logic_vector(8-1 downto 0);
    signal axi_sw_awaddr    : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_sw_awlen     : std_logic_vector(8-1 downto 0);
    signal axi_sw_awsize    : std_logic_vector(3-1 downto 0);
    signal axi_sw_awburst   : std_logic_vector(2-1 downto 0);
    signal axi_sw_awprot    : std_logic_vector(3-1 downto 0);
    signal axi_sw_awvalid   : std_logic;
    signal axi_sw_awready   : std_logic;
    signal axi_sw_wdata     : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_sw_wstrb     : std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
    signal axi_sw_wlast     : std_logic;
    signal axi_sw_wvalid    : std_logic;
    signal axi_sw_wready    : std_logic;
    signal axi_sw_bid       : std_logic_vector(8-1 downto 0);
    signal axi_sw_bresp     : std_logic_vector(2-1 downto 0);
    signal axi_sw_bvalid    : std_logic;
    signal axi_sw_bready    : std_logic;
    signal axi_sw_arid      : std_logic_vector(8-1 downto 0);
    signal axi_sw_araddr    : std_logic_vector(AXI_ADDR_WIDTH_INT-1 downto 0);
    signal axi_sw_arlen     : std_logic_vector(8-1 downto 0);
    signal axi_sw_arsize    : std_logic_vector(3-1 downto 0);
    signal axi_sw_arburst   : std_logic_vector(2-1 downto 0);
    signal axi_sw_arprot    : std_logic_vector(3-1 downto 0);
    signal axi_sw_arvalid   : std_logic;
    signal axi_sw_arready   : std_logic;
    signal axi_sw_rid       : std_logic_vector(8-1 downto 0);
    signal axi_sw_rdata     : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_sw_rresp     : std_logic_vector(2-1 downto 0);
    signal axi_sw_rlast     : std_logic;
    signal axi_sw_rvalid    : std_logic;
    signal axi_sw_rready    : std_logic;

    signal axi_awaddr_ext   : std_logic_vector(63 downto 0);
    signal axi_araddr_ext   : std_logic_vector(63 downto 0);

    signal mi_ps_dwr        : std_logic_vector(31 downto 0);
    signal mi_ps_addr       : std_logic_vector(31 downto 0);
    signal mi_ps_rd         : std_logic;
    signal mi_ps_wr         : std_logic;
    signal mi_ps_be         : std_logic_vector(3 downto 0);
    signal mi_ps_drd        : std_logic_vector(31 downto 0);
    signal mi_ps_ardy       : std_logic;
    signal mi_ps_drdy       : std_logic;

    signal mi_sync_dwr   : std_logic_vector(31 downto 0);
    signal mi_sync_addr  : std_logic_vector(31 downto 0);
    signal mi_sync_rd    : std_logic;
    signal mi_sync_wr    : std_logic;
    signal mi_sync_be    : std_logic_vector(3 downto 0);
    signal mi_sync_drd   : std_logic_vector(31 downto 0);
    signal mi_sync_ardy  : std_logic;
    signal mi_sync_drdy  : std_logic;

begin
    assert AXI_DATA_WIDTH = 32
        report "VERSAL_PS_CTRL: AXI_DATA_WIDTH generic must be 32. Actual value is: " & natural'image(AXI_DATA_WIDTH)
        severity failure;
    assert AXI_ADDR_WIDTH_INT = 32 or AXI_ADDR_WIDTH_INT = 64
        report "VERSAL_PS_CTRL: AXI_ADDR_WIDTH_INT generic must be 32 or 64. Actual value is: " & natural'image(AXI_ADDR_WIDTH_INT)
        severity failure;
    assert AXI_ADDR_WIDTH <= 64
        report "VERSAL_PS_CTRL: AXI_ADDR_WIDTH generic must be <= 64. Actual value is: " & natural'image(AXI_ADDR_WIDTH)
        severity failure;
    assert AXI_ID_WIDTH <= 8
        report "VERSAL_PS_CTRL: AXI_ID_WIDTH generic must be <= 8. Actual value is: " & natural'image(AXI_ID_WIDTH)
        severity failure;
    assert AXI_ARUSER_WIDTH /= 10 or READ_SMID(9) = '0'
        report "VERSAL_PS_CTRL: AXI_ARUSER_WIDTH generic is set to 10 and READ_SMID(9) is non zero. READ_SMID(9) must be zero to indicate PL master when AXI_ARUSER_WIDTH=10."
        severity failure;
    assert AXI_AWUSER_WIDTH /= 10 or WRITE_SMID(9) = '0'
        report "VERSAL_PS_CTRL: AXI_AWUSER_WIDTH generic is set to 10 and WRITE_SMID(9) is non zero. WRITE_SMID(9) must be zero to indicate PL master when AXI_AWUSER_WIDTH=10."
        severity failure;


    versal_fpga_id_i: entity work.VERSAL_FPGA_ID
    generic map (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH => AXI_DATA_WIDTH,
        -- Address word width in bits 32 or 64
        AXI_ADDR_WIDTH => AXI_ADDR_WIDTH_INT,
        -- Target device
        DEVICE         => DEVICE
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => AXI_LITE_CLK,
        RESET       => AXI_LITE_RESET,

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    => axi_id_awid,
        AXI_AWADDR  => axi_id_awaddr,
        AXI_AWLEN   => axi_id_awlen,
        AXI_AWSIZE  => axi_id_awsize,
        AXI_AWBURST => axi_id_awburst,
        AXI_AWPROT  => axi_id_awprot,
        AXI_AWVALID => axi_id_awvalid,
        AXI_AWREADY => axi_id_awready,
        AXI_WDATA   => axi_id_wdata,
        AXI_WSTRB   => axi_id_wstrb,
        AXI_WLAST   => axi_id_wlast,
        AXI_WVALID  => axi_id_wvalid,
        AXI_WREADY  => axi_id_wready,
        AXI_BID     => axi_id_bid,
        AXI_BRESP   => axi_id_bresp,
        AXI_BVALID  => axi_id_bvalid,
        AXI_BREADY  => axi_id_bready,
        AXI_ARID    => axi_id_arid,
        AXI_ARADDR  => axi_id_araddr,
        AXI_ARLEN   => axi_id_arlen,
        AXI_ARSIZE  => axi_id_arsize,
        AXI_ARBURST => axi_id_arburst,
        AXI_ARPROT  => axi_id_arprot,
        AXI_ARVALID => axi_id_arvalid,
        AXI_ARREADY => axi_id_arready,
        AXI_RID     => axi_id_rid,
        AXI_RDATA   => axi_id_rdata,
        AXI_RRESP   => axi_id_rresp,
        AXI_RLAST   => axi_id_rlast,
        AXI_RVALID  => axi_id_rvalid,
        AXI_RREADY  => axi_id_rready,

        -- =====================================================================
        -- FPGA_ID interface
        -- =====================================================================
        FPGA_ID     => fpga_id_int,
        FPGA_ID_VLD => fpga_id_int_vld
    );

    versal_ps_access_i: entity work.VERSAL_PS_ACCESS
    generic map (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH => AXI_DATA_WIDTH,
        -- Address word width in bits 32 or 64
        -- Use 64 if accessing via NOC, 32 otherwise
        AXI_ADDR_WIDTH => AXI_ADDR_WIDTH_INT,
        -- Target device
        DEVICE         => DEVICE
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => AXI_LITE_CLK,
        RESET       => AXI_LITE_RESET,

        -- =====================================================================
        -- Control signals
        -- =====================================================================
        ENABLE      => fpga_id_int_vld,

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR      => mi_sync_dwr,
        MI_ADDR     => mi_sync_addr,
        MI_RD       => mi_sync_rd,
        MI_WR       => mi_sync_wr,
        MI_BE       => mi_sync_be,
        MI_DRD      => mi_sync_drd,
        MI_ARDY     => mi_sync_ardy,
        MI_DRDY     => mi_sync_drdy,

        -- =====================================================================
        -- MI interface from PS (slave)
        -- =====================================================================
        MI_PS_DWR   => mi_ps_dwr,
        MI_PS_ADDR  => mi_ps_addr,
        MI_PS_RD    => mi_ps_rd,
        MI_PS_WR    => mi_ps_wr,
        MI_PS_BE    => mi_ps_be,
        MI_PS_DRD   => mi_ps_drd,
        MI_PS_ARDY  => mi_ps_ardy,
        MI_PS_DRDY  => mi_ps_drdy,

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    => axi_boot_awid,
        AXI_AWADDR  => axi_boot_awaddr,
        AXI_AWLEN   => axi_boot_awlen,
        AXI_AWSIZE  => axi_boot_awsize,
        AXI_AWBURST => axi_boot_awburst,
        AXI_AWPROT  => axi_boot_awprot,
        AXI_AWVALID => axi_boot_awvalid,
        AXI_AWREADY => axi_boot_awready,
        AXI_WDATA   => axi_boot_wdata,
        AXI_WSTRB   => axi_boot_wstrb,
        AXI_WLAST   => axi_boot_wlast,
        AXI_WVALID  => axi_boot_wvalid,
        AXI_WREADY  => axi_boot_wready,
        AXI_BID     => axi_boot_bid,
        AXI_BRESP   => axi_boot_bresp,
        AXI_BVALID  => axi_boot_bvalid,
        AXI_BREADY  => axi_boot_bready,
        AXI_ARID    => axi_boot_arid,
        AXI_ARADDR  => axi_boot_araddr,
        AXI_ARLEN   => axi_boot_arlen,
        AXI_ARSIZE  => axi_boot_arsize,
        AXI_ARBURST => axi_boot_arburst,
        AXI_ARPROT  => axi_boot_arprot,
        AXI_ARVALID => axi_boot_arvalid,
        AXI_ARREADY => axi_boot_arready,
        AXI_RID     => axi_boot_rid,
        AXI_RDATA   => axi_boot_rdata,
        AXI_RRESP   => axi_boot_rresp,
        AXI_RLAST   => axi_boot_rlast,
        AXI_RVALID  => axi_boot_rvalid,
        AXI_RREADY  => axi_boot_rready
    );

    versal_axi_switch_i: entity work.VERSAL_AXI_SWITCH
    generic map (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH => AXI_DATA_WIDTH,
        -- Address word width in bits 32 or 64
        -- Use 64 if accessing via NOC, 32 otherwise
        AXI_ADDR_WIDTH => AXI_ADDR_WIDTH_INT,
        -- Target device
        DEVICE         => DEVICE
    )
    port map (
        -- =====================================================================
        -- Select signal
        -- =====================================================================
        SEL            => fpga_id_int_vld,

        -- =====================================================================
        -- AXI4 interface (slaves)
        -- =====================================================================
        AXI_S0_AWID    => axi_id_awid,
        AXI_S0_AWADDR  => axi_id_awaddr,
        AXI_S0_AWLEN   => axi_id_awlen,
        AXI_S0_AWSIZE  => axi_id_awsize,
        AXI_S0_AWBURST => axi_id_awburst,
        AXI_S0_AWPROT  => axi_id_awprot,
        AXI_S0_AWVALID => axi_id_awvalid,
        AXI_S0_AWREADY => axi_id_awready,
        AXI_S0_WDATA   => axi_id_wdata,
        AXI_S0_WSTRB   => axi_id_wstrb,
        AXI_S0_WLAST   => axi_id_wlast,
        AXI_S0_WVALID  => axi_id_wvalid,
        AXI_S0_WREADY  => axi_id_wready,
        AXI_S0_BID     => axi_id_bid,
        AXI_S0_BRESP   => axi_id_bresp,
        AXI_S0_BVALID  => axi_id_bvalid,
        AXI_S0_BREADY  => axi_id_bready,
        AXI_S0_ARID    => axi_id_arid,
        AXI_S0_ARADDR  => axi_id_araddr,
        AXI_S0_ARLEN   => axi_id_arlen,
        AXI_S0_ARSIZE  => axi_id_arsize,
        AXI_S0_ARBURST => axi_id_arburst,
        AXI_S0_ARPROT  => axi_id_arprot,
        AXI_S0_ARVALID => axi_id_arvalid,
        AXI_S0_ARREADY => axi_id_arready,
        AXI_S0_RID     => axi_id_rid,
        AXI_S0_RDATA   => axi_id_rdata,
        AXI_S0_RRESP   => axi_id_rresp,
        AXI_S0_RLAST   => axi_id_rlast,
        AXI_S0_RVALID  => axi_id_rvalid,
        AXI_S0_RREADY  => axi_id_rready,

        AXI_S1_AWID    => axi_boot_awid,
        AXI_S1_AWADDR  => axi_boot_awaddr,
        AXI_S1_AWLEN   => axi_boot_awlen,
        AXI_S1_AWSIZE  => axi_boot_awsize,
        AXI_S1_AWBURST => axi_boot_awburst,
        AXI_S1_AWPROT  => axi_boot_awprot,
        AXI_S1_AWVALID => axi_boot_awvalid,
        AXI_S1_AWREADY => axi_boot_awready,
        AXI_S1_WDATA   => axi_boot_wdata,
        AXI_S1_WSTRB   => axi_boot_wstrb,
        AXI_S1_WLAST   => axi_boot_wlast,
        AXI_S1_WVALID  => axi_boot_wvalid,
        AXI_S1_WREADY  => axi_boot_wready,
        AXI_S1_BID     => axi_boot_bid,
        AXI_S1_BRESP   => axi_boot_bresp,
        AXI_S1_BVALID  => axi_boot_bvalid,
        AXI_S1_BREADY  => axi_boot_bready,
        AXI_S1_ARID    => axi_boot_arid,
        AXI_S1_ARADDR  => axi_boot_araddr,
        AXI_S1_ARLEN   => axi_boot_arlen,
        AXI_S1_ARSIZE  => axi_boot_arsize,
        AXI_S1_ARBURST => axi_boot_arburst,
        AXI_S1_ARPROT  => axi_boot_arprot,
        AXI_S1_ARVALID => axi_boot_arvalid,
        AXI_S1_ARREADY => axi_boot_arready,
        AXI_S1_RID     => axi_boot_rid,
        AXI_S1_RDATA   => axi_boot_rdata,
        AXI_S1_RRESP   => axi_boot_rresp,
        AXI_S1_RLAST   => axi_boot_rlast,
        AXI_S1_RVALID  => axi_boot_rvalid,
        AXI_S1_RREADY  => axi_boot_rready,

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID       => axi_sw_awid,
        AXI_AWADDR     => axi_sw_awaddr,
        AXI_AWLEN      => axi_sw_awlen,
        AXI_AWSIZE     => axi_sw_awsize,
        AXI_AWBURST    => axi_sw_awburst,
        AXI_AWPROT     => axi_sw_awprot,
        AXI_AWVALID    => axi_sw_awvalid,
        AXI_AWREADY    => axi_sw_awready,
        AXI_WDATA      => axi_sw_wdata,
        AXI_WSTRB      => axi_sw_wstrb,
        AXI_WLAST      => axi_sw_wlast,
        AXI_WVALID     => axi_sw_wvalid,
        AXI_WREADY     => axi_sw_wready,
        AXI_BID        => axi_sw_bid,
        AXI_BRESP      => axi_sw_bresp,
        AXI_BVALID     => axi_sw_bvalid,
        AXI_BREADY     => axi_sw_bready,
        AXI_ARID       => axi_sw_arid,
        AXI_ARADDR     => axi_sw_araddr,
        AXI_ARLEN      => axi_sw_arlen,
        AXI_ARSIZE     => axi_sw_arsize,
        AXI_ARBURST    => axi_sw_arburst,
        AXI_ARPROT     => axi_sw_arprot,
        AXI_ARVALID    => axi_sw_arvalid,
        AXI_ARREADY    => axi_sw_arready,
        AXI_RID        => axi_sw_rid,
        AXI_RDATA      => axi_sw_rdata,
        AXI_RRESP      => axi_sw_rresp,
        AXI_RLAST      => axi_sw_rlast,
        AXI_RVALID     => axi_sw_rvalid,
        AXI_RREADY     => axi_sw_rready
    );

    -- Translate internal signals widths to outer signals widths and setup user
    -- signals
    gen_ext_int_addresses: if AXI_ADDR_WIDTH_INT = 32 generate
        axi_araddr_ext <= X"00000000" & axi_sw_araddr;
        axi_awaddr_ext <= X"00000000" & axi_sw_awaddr;
    else generate
        axi_araddr_ext <= axi_sw_araddr;
        axi_awaddr_ext <= axi_sw_awaddr;
    end generate;

    AXI_AWID       <= axi_sw_awid(AXI_ID_WIDTH - 1 downto 0);
    AXI_AWADDR     <= axi_awaddr_ext(AXI_ADDR_WIDTH - 1 downto 0);
    AXI_AWUSER     <= WRITE_SMID;
    AXI_AWLEN      <= axi_sw_awlen;
    AXI_AWSIZE     <= axi_sw_awsize;
    AXI_AWBURST    <= axi_sw_awburst;
    AXI_AWPROT     <= axi_sw_awprot;
    AXI_AWVALID    <= axi_sw_awvalid;
    axi_sw_awready <= AXI_AWREADY;
    AXI_WDATA      <= axi_sw_wdata;
    AXI_WSTRB      <= axi_sw_wstrb;
    AXI_WLAST      <= axi_sw_wlast;
    AXI_WVALID     <= axi_sw_wvalid;
    axi_sw_wready  <= AXI_WREADY;
    axi_sw_bid     <= std_logic_vector(resize(unsigned(AXI_BID), axi_sw_bid'length));
    axi_sw_bresp   <= AXI_BRESP;
    axi_sw_bvalid  <= AXI_BVALID;
    AXI_BREADY     <= axi_sw_bready;
    AXI_ARID       <= axi_sw_arid(AXI_ID_WIDTH - 1 downto 0);
    AXI_ARADDR     <= axi_araddr_ext(AXI_ADDR_WIDTH - 1 downto 0);
    AXI_ARUSER     <= READ_SMID;
    AXI_ARLEN      <= axi_sw_arlen;
    AXI_ARSIZE     <= axi_sw_arsize;
    AXI_ARBURST    <= axi_sw_arburst;
    AXI_ARPROT     <= axi_sw_arprot;
    AXI_ARVALID    <= axi_sw_arvalid;
    axi_sw_arready <= AXI_ARREADY;
    axi_sw_rid     <= std_logic_vector(resize(unsigned(AXI_RID), axi_sw_rid'length));
    axi_sw_rdata   <= AXI_RDATA;
    axi_sw_rresp   <= AXI_RRESP;
    axi_sw_rlast   <= AXI_RLAST;
    axi_sw_rvalid  <= AXI_RVALID;
    AXI_RREADY     <= axi_sw_rready;

    AXI_ARCACHE <= "0000";
    AXI_ARLOCK  <= '0';
    AXI_ARQOS   <= "0000";

    AXI_AWCACHE <= "0000";
    AXI_AWLOCK  <= '0';
    AXI_AWQOS   <= "0000";

    axi4lite2mi_i: entity work.AXI4LITE2MI
    generic map (
        -- Data word width in bits, must be 32
        DATA_WIDTH  => 32,
        -- Address word width in bits
        ADDR_WIDTH  => 32,
        -- Address mask vector
        ADDR_MASK   => (others => '1'),
        -- Target device
        DEVICE      => DEVICE
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => AXI_LITE_CLK,
        RESET       => AXI_LITE_RESET,

        -- =====================================================================
        -- AXI4-Lite interface (slave)
        -- =====================================================================
        AXI_AWADDR  => AXI_LITE_AWADDR,
        AXI_AWVALID => AXI_LITE_AWVALID,
        AXI_AWREADY => AXI_LITE_AWREADY,

        AXI_WDATA   => AXI_LITE_WDATA,
        AXI_WSTRB   => AXI_LITE_WSTRB,
        AXI_WVALID  => AXI_LITE_WVALID,
        AXI_WREADY  => AXI_LITE_WREADY,

        AXI_BRESP   => AXI_LITE_BRESP,
        AXI_BVALID  => AXI_LITE_BVALID,
        AXI_BREADY  => AXI_LITE_BREADY,

        AXI_ARADDR  => AXI_LITE_ARADDR,
        AXI_ARVALID => AXI_LITE_ARVALID,
        AXI_ARREADY => AXI_LITE_ARREADY,

        AXI_RDATA   => AXI_LITE_RDATA,
        AXI_RRESP   => AXI_LITE_RRESP,
        AXI_RVALID  => AXI_LITE_RVALID,
        AXI_RREADY  => AXI_LITE_RREADY,

        -- =====================================================================
        -- MI interface (master)
        -- =====================================================================
        MI_DWR      => mi_ps_dwr,
        MI_ADDR     => mi_ps_addr,
        MI_RD       => mi_ps_rd,
        MI_WR       => mi_ps_wr,
        MI_BE       => mi_ps_be,
        MI_DRD      => mi_ps_drd,
        MI_ARDY     => mi_ps_ardy,
        MI_DRDY     => mi_ps_drdy
    );

    mi_async_i: entity work.MI_ASYNC
    generic map (
        DATA_WIDTH  => 32,
        ADDR_WIDTH  => 32,
        META_WIDTH  => 1,
        RAM_TYPE    => "LUT",
        RESET_LOGIC => true,
        DEVICE      => DEVICE
    )
    port map (
        CLK_M     => CLK,
        RESET_M   => RESET,

        MI_M_DWR  => MI_DWR,
        MI_M_ADDR => MI_ADDR,
        MI_M_RD   => MI_RD,
        MI_M_WR   => MI_WR,
        MI_M_BE   => MI_BE,
        MI_M_DRD  => MI_DRD,
        MI_M_ARDY => MI_ARDY,
        MI_M_DRDY => MI_DRDY,

        CLK_S     => AXI_LITE_CLK,
        RESET_S   => AXI_LITE_RESET,
        MI_S_DWR  => mi_sync_dwr,
        MI_S_ADDR => mi_sync_addr,
        MI_S_RD   => mi_sync_rd,
        MI_S_WR   => mi_sync_wr,
        MI_S_BE   => mi_sync_be,
        MI_S_DRD  => mi_sync_drd,
        MI_S_ARDY => mi_sync_ardy,
        MI_S_DRDY => mi_sync_drdy
    );

    sync_fpga_id_i: entity work.SYNC_FPGA_ID
    generic map (
        SAME_CLOCKS        => false,
        DEVICE             => DEVICE,
        FPGA_ID_WIDTH      => 128
    )
    port map (
        CLK              => CLK,
        RESET            => RESET,
        FPGA_ID_CLK      => AXI_LITE_CLK,
        FPGA_ID_RESET    => AXI_LITE_RESET,

        FPGA_ID          => fpga_id_int,
        FPGA_ID_VLD      => fpga_id_int_vld,

        SYNC_FPGA_ID     => FPGA_ID,
        SYNC_FPGA_ID_VLD => FPGA_ID_VLD
    );

end architecture;




