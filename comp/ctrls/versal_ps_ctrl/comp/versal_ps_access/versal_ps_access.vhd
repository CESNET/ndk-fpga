-- versal_ps_access.vhd : Access bridge to Versal PS address space via MI bus
--                        This component is mainly intended for boot/flashing
--                        of versal based cards. However, whole PS/NOC address
--                        space is accessible. Any access to this component
--                        must be sw locked because mixing accesses from
--                        multiple processes can lead to data corruption, etc.
--                        The bridge also contains registers for communication
--                        between SW drivers and PS BMC.
-- Copyright (C) DynaNIC Semiconductors, Ltd.
-- Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2024
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;

entity VERSAL_PS_ACCESS is
    generic (
        -- AXI data word width in bits 32
        AXI_DATA_WIDTH : natural := 32;
        -- Address word width in bits 32 or 64
        -- Use 64 if accessing via NOC, 32 otherwise
        AXI_ADDR_WIDTH : natural := 32;
        -- Target device
        DEVICE         : string  := "VERSAL"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         : in  std_logic;
        RESET       : in  std_logic;

        -- =====================================================================
        -- Control signals
        -- =====================================================================
        ENABLE      : in std_logic;

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR      : in  std_logic_vector(31 downto 0);
        MI_ADDR     : in  std_logic_vector(31 downto 0);
        MI_RD       : in  std_logic;
        MI_WR       : in  std_logic;
        MI_BE       : in  std_logic_vector(3 downto 0);
        MI_DRD      : out std_logic_vector(31 downto 0);
        MI_ARDY     : out std_logic;
        MI_DRDY     : out std_logic;

        -- =====================================================================
        -- MI interface from PS (slave)
        -- =====================================================================
        MI_PS_DWR      : in  std_logic_vector(31 downto 0) := (others => '0');
        MI_PS_ADDR     : in  std_logic_vector(31 downto 0) := (others => '0');
        MI_PS_RD       : in  std_logic := '0';
        MI_PS_WR       : in  std_logic := '0';
        MI_PS_BE       : in  std_logic_vector(3 downto 0) := (others => '0');
        MI_PS_DRD      : out std_logic_vector(31 downto 0);
        MI_PS_ARDY     : out std_logic;
        MI_PS_DRDY     : out std_logic;

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    : out std_logic_vector(8-1 downto 0);
        AXI_AWADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_AWLEN   : out std_logic_vector(8-1 downto 0);
        AXI_AWSIZE  : out std_logic_vector(3-1 downto 0);
        AXI_AWBURST : out std_logic_vector(2-1 downto 0);
        AXI_AWPROT  : out std_logic_vector(3-1 downto 0);
        AXI_AWVALID : out std_logic;
        AXI_AWREADY : in  std_logic;
        AXI_WDATA   : out std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_WSTRB   : out std_logic_vector((AXI_DATA_WIDTH/8)-1 downto 0);
        AXI_WLAST   : out std_logic;
        AXI_WVALID  : out std_logic;
        AXI_WREADY  : in  std_logic;
        AXI_BID     : in  std_logic_vector(8-1 downto 0);
        AXI_BRESP   : in  std_logic_vector(2-1 downto 0);
        AXI_BVALID  : in  std_logic;
        AXI_BREADY  : out std_logic;
        AXI_ARID    : out std_logic_vector(8-1 downto 0);
        AXI_ARADDR  : out std_logic_vector(AXI_ADDR_WIDTH-1 downto 0);
        AXI_ARLEN   : out std_logic_vector(8-1 downto 0);
        AXI_ARSIZE  : out std_logic_vector(3-1 downto 0);
        AXI_ARBURST : out std_logic_vector(2-1 downto 0);
        AXI_ARPROT  : out std_logic_vector(3-1 downto 0);
        AXI_ARVALID : out std_logic;
        AXI_ARREADY : in  std_logic;
        AXI_RID     : in  std_logic_vector(8-1 downto 0);
        AXI_RDATA   : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        AXI_RRESP   : in  std_logic_vector(2-1 downto 0);
        AXI_RLAST   : in  std_logic;
        AXI_RVALID  : in  std_logic;
        AXI_RREADY  : out std_logic
    );

end entity;

architecture FULL of VERSAL_PS_ACCESS is
    constant MI_PORTS             : natural := 2;
    -- Address width used from mi address
    constant USED_ADDR_WIDTH      : natural := 11;
    -- Address space of the component, synchronize address space window with USED_ADDR_WIDTH
    constant MI_ADDR_BASE         : slv_array_t(MI_PORTS-1 downto 0)(32-1 downto 0) := (
        0 => X"0000_0000",     -- Address control & BMC communication
        1 => X"0000_0800"      -- Address space window
    );
    -- Pending window accesses: at most 4 writes before the AXI address phase or 1 read before its data
    constant BEAT_CNT_WIDTH       : natural := 4;
    constant STATUS_REG_ADDR      : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000000000";
    constant UPPER_ADDR_REG_ADDR  : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000000100";
    constant LOWER_ADDR_REG_ADDR  : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000001000";
    constant BMC_STATUS_ADDR      : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000001100";
    constant BMC_CONTROL_ADDR     : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000010000";
    constant BMC_ERASE_START_ADDR : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000010100";
    constant BMC_ERASE_SIZE_ADDR  : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000011000";

    -- Address space from the PS interface perspective
    -- NOTE: BMC registers are writeble from both driver and PS. Driver and BMC must avoid simultanous
    --       writes by observing proper communication protocol. Otherwise, one of the writes will be lost.
    --       Status reg has BMC write priority, other registers have driver write priority on simultanous
    --       writes.
    constant BMC_STATUS_ADDR_PS      : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000000000";
    constant BMC_CONTROL_ADDR_PS     : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000000100";
    constant BMC_ERASE_START_ADDR_PS : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000001000";
    constant BMC_ERASE_SIZE_ADDR_PS  : std_logic_vector(USED_ADDR_WIDTH - 1 downto 0) := "00000001100";

    signal mi_int_dwr        : slv_array_t     (MI_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_int_addr       : slv_array_t     (MI_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_int_be         : slv_array_t     (MI_PORTS-1 downto 0)(32/8-1 downto 0);
    signal mi_int_rd         : std_logic_vector(MI_PORTS-1 downto 0);
    signal mi_int_wr         : std_logic_vector(MI_PORTS-1 downto 0);
    signal mi_int_drd        : slv_array_t     (MI_PORTS-1 downto 0)(32-1 downto 0);
    signal mi_int_ardy       : std_logic_vector(MI_PORTS-1 downto 0);
    signal mi_int_drdy       : std_logic_vector(MI_PORTS-1 downto 0);

    signal axi_awaddr_ext    : std_logic_vector(32-1 downto 0);
    signal axi_araddr_ext    : std_logic_vector(32-1 downto 0);

    signal upper_addr_reg      : std_logic_vector(31 downto 0) := (others => '0');
    signal lower_addr_reg      : std_logic_vector(31 downto 0) := (others => '0');
    signal bmc_control_reg     : std_logic_vector(31 downto 0) := (others => '0');
    signal bmc_status_reg      : std_logic_vector(31 downto 0) := (others => '0');
    signal bmc_erase_start_reg : std_logic_vector(31 downto 0) := (others => '0');
    signal bmc_erase_size_reg  : std_logic_vector(31 downto 0) := (others => '0');

    signal upper_addr_reg_we      : std_logic;
    signal lower_addr_reg_we      : std_logic;
    signal bmc_control_reg_we     : std_logic;
    signal bmc_status_reg_we      : std_logic;
    signal bmc_erase_start_reg_we : std_logic;
    signal bmc_erase_size_reg_we  : std_logic;

    signal bmc_control_reg_we_ps     : std_logic;
    signal bmc_status_reg_we_ps      : std_logic;
    signal bmc_erase_start_reg_we_ps : std_logic;
    signal bmc_erase_size_reg_we_ps  : std_logic;

    signal use_64            : std_logic;
    signal busy              : std_logic;

    signal axi_arw_beat      : std_logic;
    signal mi_rw_beat        : std_logic;

    signal axi_beat_reg      : std_logic_vector(BEAT_CNT_WIDTH-1 downto 0) := (others => '0');
    signal mi_beat_reg       : std_logic_vector(BEAT_CNT_WIDTH-1 downto 0) := (others => '0');

    signal beat_reg_rst      : std_logic;
    signal mi_addr_reg_wr    : std_logic;
    signal beats_same        : std_logic;

begin
    assert AXI_DATA_WIDTH = 32
        report "VERSAL_PS_ACCESS: AXI_DATA_WIDTH generic must be 32. Actual value is: " & natural'image(AXI_DATA_WIDTH)
        severity failure;
    assert AXI_ADDR_WIDTH = 32 or AXI_ADDR_WIDTH = 64
        report "VERSAL_PS_ACCESS: AXI_ADDR_WIDTH generic must be 32 or 64. Actual value is: " & natural'image(AXI_ADDR_WIDTH)
        severity failure;

    busy <= not ENABLE or not beats_same;

    mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map (
        ADDR_WIDTH    => 32,
        DATA_WIDTH    => 32,
        PORTS         => MI_PORTS,
        PIPE_OUTREG   => true,
        ADDR_BASE     => MI_ADDR_BASE,
        DEVICE        => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DWR     => MI_DWR,
        RX_ADDR    => MI_ADDR,
        RX_BE      => MI_BE,
        RX_RD      => MI_RD,
        RX_WR      => MI_WR,
        RX_ARDY    => MI_ARDY,
        RX_DRD     => MI_DRD,
        RX_DRDY    => MI_DRDY,

        TX_DWR     => mi_int_dwr,
        TX_ADDR    => mi_int_addr,
        TX_BE      => mi_int_be,
        TX_RD      => mi_int_rd,
        TX_WR      => mi_int_wr,
        TX_ARDY    => mi_int_ardy,
        TX_DRD     => mi_int_drd,
        TX_DRDY    => mi_int_drdy
    );

    mi2axi4_i: entity work.MI2AXI4
    generic map (
        -- MI data word width in bits, must be 32
        MI_DATA_WIDTH  => 32,
        -- AXI data word width in bits, 32 or 64
        AXI_DATA_WIDTH => 32,
        -- Address word width in bits
        ADDR_WIDTH     => 32,
        -- Address mask vector
        ADDR_MASK      => (others => '1'),
        -- Target device
        DEVICE         => DEVICE
    )
    port map (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK         => CLK,
        RESET       => RESET,

        -- =====================================================================
        -- MI interface (slave)
        -- =====================================================================
        MI_DWR     => mi_int_dwr(1),
        MI_ADDR    => mi_int_addr(1),
        MI_RD      => mi_int_rd(1),
        MI_WR      => mi_int_wr(1),
        MI_BE      => mi_int_be(1),
        MI_DRD     => mi_int_drd(1),
        MI_ARDY    => mi_int_ardy(1),
        MI_DRDY    => mi_int_drdy(1),

        -- =====================================================================
        -- AXI4 interface (master)
        -- =====================================================================
        AXI_AWID    => AXI_AWID,
        AXI_AWADDR  => axi_awaddr_ext,
        AXI_AWLEN   => AXI_AWLEN,
        AXI_AWSIZE  => AXI_AWSIZE,
        AXI_AWBURST => open,
        AXI_AWPROT  => AXI_AWPROT,
        AXI_AWVALID => AXI_AWVALID,
        AXI_AWREADY => AXI_AWREADY,
        AXI_WDATA   => AXI_WDATA,
        AXI_WSTRB   => AXI_WSTRB,
        AXI_WVALID  => AXI_WVALID,
        AXI_WREADY  => AXI_WREADY,
        AXI_BID     => AXI_BID,
        AXI_BRESP   => AXI_BRESP,
        AXI_BVALID  => AXI_BVALID,
        AXI_BREADY  => AXI_BREADY,
        AXI_ARID    => AXI_ARID,
        AXI_ARADDR  => axi_araddr_ext,
        AXI_ARLEN   => AXI_ARLEN,
        AXI_ARSIZE  => AXI_ARSIZE,
        AXI_ARBURST => open,
        AXI_ARPROT  => AXI_ARPROT,
        AXI_ARVALID => AXI_ARVALID,
        AXI_ARREADY => AXI_ARREADY,
        AXI_RID     => AXI_RID,
        AXI_RDATA   => AXI_RDATA,
        AXI_RRESP   => AXI_RRESP,
        AXI_RLAST   => AXI_RLAST,
        AXI_RVALID  => AXI_RVALID,
        AXI_RREADY  => AXI_RREADY
    );

    gen_64_addr_g: if AXI_ADDR_WIDTH = 64 generate
        AXI_AWADDR <= upper_addr_reg & lower_addr_reg(31 downto USED_ADDR_WIDTH) & axi_awaddr_ext(USED_ADDR_WIDTH - 1 downto 0);
        AXI_ARADDR <= upper_addr_reg & lower_addr_reg(31 downto USED_ADDR_WIDTH) & axi_araddr_ext(USED_ADDR_WIDTH - 1 downto 0);
    end generate;

    gen_32_addr_g: if AXI_ADDR_WIDTH = 32 generate
        AXI_AWADDR <= lower_addr_reg(31 downto USED_ADDR_WIDTH) & axi_awaddr_ext(USED_ADDR_WIDTH - 1 downto 0);
        AXI_ARADDR <= lower_addr_reg(31 downto USED_ADDR_WIDTH) & axi_araddr_ext(USED_ADDR_WIDTH - 1 downto 0);
    end generate;

    AXI_WLAST <= '1';

    AXI_AWBURST <= "01";
    AXI_ARBURST <= "01";

    axi_beat_cnt_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (beat_reg_rst = '1') then
                axi_beat_reg <= (others => '0');
            elsif (axi_arw_beat = '1') then
                axi_beat_reg <= std_logic_vector(unsigned(axi_beat_reg) + to_unsigned(1, axi_beat_reg'length));
            end if;
        end if;
    end process;

    mi_beat_cnt_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (beat_reg_rst = '1') then
                mi_beat_reg <= (others => '0');
            elsif (mi_rw_beat = '1') then
                mi_beat_reg <= std_logic_vector(unsigned(mi_beat_reg) + to_unsigned(1, mi_beat_reg'length));
            end if;
        end if;
    end process;

    axi_arw_beat <= (AXI_AWVALID and AXI_AWREADY) or (AXI_ARVALID and AXI_ARREADY);
    mi_rw_beat   <= (MI_RD or MI_WR) and MI_ARDY and MI_ADDR(USED_ADDR_WIDTH);

    mi_addr_reg_wr <= '1' when MI_WR = '1' and MI_ARDY = '1' and MI_ADDR(USED_ADDR_WIDTH) = '0' and
                               (MI_ADDR(USED_ADDR_WIDTH - 1 downto 0) = UPPER_ADDR_REG_ADDR or
                                MI_ADDR(USED_ADDR_WIDTH - 1 downto 0) = LOWER_ADDR_REG_ADDR) else
                      '0';

    beat_reg_rst <= RESET or mi_addr_reg_wr;

    beats_same <= '1' when axi_beat_reg = mi_beat_reg else '0';

    upper_addr_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                upper_addr_reg <= (others => '0');
            else
                if (upper_addr_reg_we = '1') then
                    upper_addr_reg <= mi_int_dwr(0);
                end if;
            end if;
        end if;
    end process;

    lower_addr_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                lower_addr_reg <= (others => '0');
            else
                if (lower_addr_reg_we = '1') then
                    lower_addr_reg <= mi_int_dwr(0);
                end if;
            end if;
        end if;
    end process;

    bmc_control_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (bmc_control_reg_we = '1') then
                bmc_control_reg <= mi_int_dwr(0);
            else
                if (bmc_control_reg_we_ps = '1') then
                    bmc_control_reg <= MI_PS_DWR;
                end if;
            end if;
        end if;
    end process;

    bmc_status_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (bmc_status_reg_we_ps = '1') then
                bmc_status_reg <= MI_PS_DWR;
            else
                if (bmc_status_reg_we = '1') then
                    bmc_status_reg <= mi_int_dwr(0);
                end if;
            end if;
        end if;
    end process;

    bmc_erase_start_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (bmc_erase_start_reg_we = '1') then
                bmc_erase_start_reg <= mi_int_dwr(0);
            else
                if (bmc_erase_start_reg_we_ps = '1') then
                    bmc_erase_start_reg <= MI_PS_DWR;
                end if;
            end if;
        end if;
    end process;

    bmc_erase_size_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (bmc_erase_size_reg_we = '1') then
                bmc_erase_size_reg <= mi_int_dwr(0);
            else
                if (bmc_erase_size_reg_we_ps = '1') then
                    bmc_erase_size_reg <= MI_PS_DWR;
                end if;
            end if;
        end if;
    end process;

    -- Driver side MI control
    upper_addr_reg_we      <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = UPPER_ADDR_REG_ADDR else '0';
    lower_addr_reg_we      <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = LOWER_ADDR_REG_ADDR else '0';
    bmc_control_reg_we     <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = BMC_CONTROL_ADDR else '0';
    bmc_status_reg_we      <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = BMC_STATUS_ADDR else '0';
    bmc_erase_start_reg_we <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = BMC_ERASE_START_ADDR else '0';
    bmc_erase_size_reg_we  <= '1' when mi_int_wr(0) = '1' and mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) = BMC_ERASE_SIZE_ADDR else '0';

    mi_int_ardy(0) <= mi_int_wr(0) or mi_int_rd(0);
    mi_int_drdy(0) <= mi_int_rd(0);

    use_64 <= '1' when AXI_ADDR_WIDTH = 64 else '0';

    with mi_int_addr(0)(USED_ADDR_WIDTH - 1 downto 0) select mi_int_drd(0) <=
        (31 downto 2 => '0', 1 => use_64, 0 => busy) when STATUS_REG_ADDR,
        upper_addr_reg when UPPER_ADDR_REG_ADDR,
        lower_addr_reg when LOWER_ADDR_REG_ADDR,
        bmc_control_reg when BMC_CONTROL_ADDR,
        bmc_status_reg when BMC_STATUS_ADDR,
        bmc_erase_start_reg when BMC_ERASE_START_ADDR,
        bmc_erase_size_reg when BMC_ERASE_SIZE_ADDR,
        X"00000000" when others;

    -- BMC side MI control
    bmc_control_reg_we_ps     <= '1' when MI_PS_WR = '1' and MI_PS_ADDR(USED_ADDR_WIDTH - 1 downto 0) = BMC_CONTROL_ADDR_PS else '0';
    bmc_status_reg_we_ps      <= '1' when MI_PS_WR = '1' and MI_PS_ADDR(USED_ADDR_WIDTH - 1 downto 0) = BMC_STATUS_ADDR_PS else '0';
    bmc_erase_start_reg_we_ps <= '1' when MI_PS_WR = '1' and MI_PS_ADDR(USED_ADDR_WIDTH - 1 downto 0) = BMC_ERASE_START_ADDR_PS else '0';
    bmc_erase_size_reg_we_ps  <= '1' when MI_PS_WR = '1' and MI_PS_ADDR(USED_ADDR_WIDTH - 1 downto 0) = BMC_ERASE_SIZE_ADDR_PS else '0';

    MI_PS_ARDY <= MI_PS_WR or MI_PS_RD;
    MI_PS_DRDY <= MI_PS_RD;

    with MI_PS_ADDR(USED_ADDR_WIDTH - 1 downto 0) select MI_PS_DRD <=
        bmc_control_reg when BMC_CONTROL_ADDR_PS,
        bmc_status_reg when BMC_STATUS_ADDR_PS,
        bmc_erase_start_reg when BMC_ERASE_START_ADDR_PS,
        bmc_erase_size_reg when BMC_ERASE_SIZE_ADDR_PS,
        X"00000000" when others;

end architecture;
