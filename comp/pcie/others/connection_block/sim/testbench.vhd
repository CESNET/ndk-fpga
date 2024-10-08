-- testbench.vhd: Testbench VHDL file
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

entity testbench is
end testbench;

architecture FULL of testbench is

    -- BAR0 base address for PCIE->MI32 transalation
    constant BAR0_BASE_ADDR         : std_logic_vector(31 downto 0) := X"00000000";
    -- BAR1 base address for PCIE->MI32 transalation
    constant BAR1_BASE_ADDR         : std_logic_vector(31 downto 0) := X"00000000";
    -- BAR2 base address for PCIE->MI32 transalation
    constant BAR2_BASE_ADDR         : std_logic_vector(31 downto 0) := X"04000000";
    -- BAR3 base address for PCIE->MI32 transalation
    constant BAR3_BASE_ADDR         : std_logic_vector(31 downto 0) := X"04000000";
    -- BAR4 base address for PCIE->MI32 transalation
    constant BAR4_BASE_ADDR         : std_logic_vector(31 downto 0) := X"08000000";
    -- BAR5 base address for PCIE->MI32 transalation
    constant BAR5_BASE_ADDR         : std_logic_vector(31 downto 0) := X"08000000";
    -- Expansion ROM base address for PCIE->MI32 transalation
    constant EXP_ROM_BASE_ADDR      : std_logic_vector(31 downto 0) := X"0A000000";

    -- Number of items in FIFO for data read from FPGA
    constant AXI2MI_FIFO_SIZE       : integer := 16;

    -- MAX_PAYLOAD_SIZE:
    -- 000b: 128 bytes maximum payload size
    -- 001b: 256 bytes maximum payload size
    -- 010b: 512 bytes maximum payload size
    -- 011b: 1024 bytes maximum payload size
    constant MAX_PAYLOAD_SIZE : std_logic_vector(2 downto 0) := "011";
    constant AXI_DATA_WIDTH   : natural := 512;
    constant AXI_CQUSER_WIDTH : natural := 183;
    constant AXI_CCUSER_WIDTH : natural := 81;

    constant MFB_REGIONS      : integer := 2;   -- Number of regions in word
    constant MFB_REG_SIZE     : integer := 1;   -- Number of blocks in region
    constant MFB_BLOCK_SIZE   : integer := 8;   -- Number of items in block
    constant MFB_ITEM_WIDTH   : integer := 32;  -- Width of one item (in bits)

    constant DEVICE           : string  := "STRATIX10";

    constant CLK_PERIOD         : time := 5 ns;
    constant RESET_TIME         : time := 5 * CLK_PERIOD;

    constant WR_PCIE_PKT : std_logic_vector(127 downto 0) := X"CAFEDEAD" &
                                                             X"4C000004" &
                                                             X"0042010F" &
                                                             X"40000001";

    constant RD_PCIE_PKT : std_logic_vector(127 downto 0) := X"DEADDEAD" &
                                                             X"4C000000" &
                                                             X"0042020F" &
                                                             X"00000001";

    constant SSPL_PCIE_PKT : std_logic_vector(127 downto 0) := X"BEEFBEEF" &
                                                             X"00000000" &
                                                             X"00420250" &
                                                             X"74000001";

    signal clk               : std_logic;
    signal reset             : std_logic;

    signal pcie_avst_rx_ready     : std_logic;
    signal pcie_avst_rx_sop       : std_logic_vector(1 downto 0);
    signal pcie_avst_rx_eop       : std_logic_vector(1 downto 0);
    signal pcie_avst_rx_data      : std_logic_vector(511 downto 0);
    signal pcie_avst_rx_valid     : std_logic_vector(1 downto 0);
    signal pcie_avst_rx_empty     : std_logic_vector(5 downto 0);
    signal pcie_avst_rx_bar_range : std_logic_vector(5 downto 0);

    signal axi_cq_data           : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_cq_user           : std_logic_vector(AXI_CQUSER_WIDTH-1 downto 0);
    signal axi_cq_last           : std_logic;
    signal axi_cq_keep           : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
    signal axi_cq_valid          : std_logic;
    signal axi_cq_ready          : std_logic;

    signal mi_dwr            : std_logic_vector(31 downto 0);
    signal mi_addr           : std_logic_vector(31 downto 0);
    signal mi_be             : std_logic_vector(3 downto 0);
    signal mi_rd             : std_logic;
    signal mi_wr             : std_logic;
    signal mi_drd            : std_logic_vector(31 downto 0);
    signal mi_ardy           : std_logic;
    signal mi_drdy           : std_logic;

    signal s_scratch_reg_sel    : std_logic;
    signal s_scratch_reg_we     : std_logic;
    signal s_scratch_reg        : std_logic_vector(32-1 downto 0);
    signal s_control_reg_sel    : std_logic;
    signal s_control_reg_we     : std_logic;
    signal s_control_reg        : std_logic_vector(32-1 downto 0);

    signal axi_cc_data           : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal axi_cc_user           : std_logic_vector(AXI_CCUSER_WIDTH-1 downto 0);
    signal axi_cc_last           : std_logic;
    signal axi_cc_keep           : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
    signal axi_cc_valid          : std_logic;
    signal axi_cc_ready          : std_logic;

    signal pcie_avst_tx_sop   : std_logic_vector(1 downto 0);
    signal pcie_avst_tx_eop   : std_logic_vector(1 downto 0);
    signal pcie_avst_tx_data  : std_logic_vector(511 downto 0);
    signal pcie_avst_tx_valid : std_logic_vector(1 downto 0);
    signal pcie_avst_tx_err   : std_logic_vector(1 downto 0);
    signal pcie_avst_tx_ready : std_logic;

    signal ptc_up_mfb_data        : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ptc_up_mfb_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ptc_up_mfb_eof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ptc_up_mfb_sof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal ptc_up_mfb_eof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ptc_up_mfb_src_rdy     : std_logic := '0';
    signal ptc_up_mfb_dst_rdy     : std_logic;

    signal ptc_down_mfb_data      : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ptc_down_mfb_sof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ptc_down_mfb_eof       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal ptc_down_mfb_sof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal ptc_down_mfb_eof_pos   : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal ptc_down_mfb_src_rdy   : std_logic;
    signal ptc_down_mfb_dst_rdy   : std_logic := '1';

begin

    pcie_avst_tx_ready <= '1';

    clk_gen : process
    begin
        clk <= '1';
        wait for CLK_PERIOD / 2;
        clk <= '0';
        wait for CLK_PERIOD / 2;
    end process;

    reset_gen : process
    begin
        reset <= '1';
        wait for RESET_TIME;
        reset <= '0';
        wait;
    end process;

    pcie_connection_block_i : entity work.PCIE_CONNECTION_BLOCK
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REG_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK               => clk,
        RESET             => reset,
        -- =====================================================================
        -- TO/FROM STRATIX 10 PCIE H-TILE IP CORE
        -- =====================================================================
        -- DOWN stream
        RX_AVST_DATA      => pcie_avst_rx_data,
		RX_AVST_SOP       => pcie_avst_rx_sop,
		RX_AVST_EOP       => pcie_avst_rx_eop,
        RX_AVST_EMPTY     => pcie_avst_rx_empty,
        RX_AVST_BAR_RANGE => pcie_avst_rx_bar_range,
        RX_AVST_VALID     => pcie_avst_rx_valid,
		RX_AVST_READY     => pcie_avst_rx_ready,
        -- UP stream
        TX_AVST_DATA      => pcie_avst_tx_data,
        TX_AVST_SOP       => pcie_avst_tx_sop,
        TX_AVST_EOP       => pcie_avst_tx_eop,
        TX_AVST_ERROR     => pcie_avst_tx_err,
        TX_AVST_VALID     => pcie_avst_tx_valid,
        TX_AVST_READY     => pcie_avst_tx_ready,
        -- =====================================================================
        -- TO/FROM PCIE TRANSACTION CONTROLER (PTC)
        -- =====================================================================
        -- UP stream
        RX_MFB_DATA       => ptc_up_mfb_data,
        RX_MFB_SOF        => ptc_up_mfb_sof,
        RX_MFB_EOF        => ptc_up_mfb_eof,
        RX_MFB_SOF_POS    => ptc_up_mfb_sof_pos,
        RX_MFB_EOF_POS    => ptc_up_mfb_eof_pos,
        RX_MFB_SRC_RDY    => ptc_up_mfb_src_rdy,
        RX_MFB_DST_RDY    => ptc_up_mfb_dst_rdy,
        -- DOWN stream
        TX_MFB_DATA       => ptc_down_mfb_data,
        TX_MFB_SOF        => ptc_down_mfb_sof,
        TX_MFB_EOF        => ptc_down_mfb_eof,
        TX_MFB_SOF_POS    => ptc_down_mfb_sof_pos,
        TX_MFB_EOF_POS    => ptc_down_mfb_eof_pos,
        TX_MFB_SRC_RDY    => ptc_down_mfb_src_rdy,
        TX_MFB_DST_RDY    => ptc_down_mfb_dst_rdy,
        -- =====================================================================
        -- TO/FROM MI32 TRANSACTION CONTROLER (AXI2MI)
        -- =====================================================================
        -- UP stream
        RX_AXI_CC_DATA    => axi_cc_data,
        RX_AXI_CC_USER    => axi_cc_user,
        RX_AXI_CC_LAST    => axi_cc_last,
        RX_AXI_CC_KEEP    => axi_cc_keep,
        RX_AXI_CC_VALID   => axi_cc_valid,
        RX_AXI_CC_READY   => axi_cc_ready,
        -- DOWN stream
        TX_AXI_CQ_DATA    => axi_cq_data,
        TX_AXI_CQ_USER    => axi_cq_user,
        TX_AXI_CQ_LAST    => axi_cq_last,
        TX_AXI_CQ_KEEP    => axi_cq_keep,
        TX_AXI_CQ_VALID   => axi_cq_valid,
        TX_AXI_CQ_READY   => axi_cq_ready
    );

    axi2mi_i : entity work.axi2mi
    generic map (
        AXI_DATA_WIDTH    => AXI_DATA_WIDTH,
        AXI_CQUSER_WIDTH  => AXI_CQUSER_WIDTH,
        AXI_CCUSER_WIDTH  => AXI_CCUSER_WIDTH,

        BAR0_BASE_ADDR    => BAR0_BASE_ADDR,
        BAR1_BASE_ADDR    => BAR1_BASE_ADDR,
        BAR2_BASE_ADDR    => BAR2_BASE_ADDR,
        BAR3_BASE_ADDR    => BAR3_BASE_ADDR,
        BAR4_BASE_ADDR    => BAR4_BASE_ADDR,
        BAR5_BASE_ADDR    => BAR5_BASE_ADDR,
        EXP_ROM_BASE_ADDR => EXP_ROM_BASE_ADDR,

        FIFO_SIZE         => AXI2MI_FIFO_SIZE,

        AXI_PIPE          => false,
        MI_PIPE           => false,
        DEVICE            => DEVICE
    )
    port map (
        -- Common signals
        CLK               => clk,
        RESET             => reset,

        -- Completer Request Interface (CQ)
        CQ_DATA           => axi_cq_data,
        CQ_USER           => axi_cq_user,
        CQ_LAST           => axi_cq_last,
        CQ_KEEP           => axi_cq_keep,
        CQ_VALID          => axi_cq_valid,
        CQ_READY          => axi_cq_ready,

        CQ_NP_REQ         => open,
        CQ_NP_REQ_COUNT   => (others => '1'),

        -- Completer Completion Interface (CC)
        CC_DATA           => axi_cc_data,
        CC_USER           => axi_cc_user,
        CC_LAST           => axi_cc_last,
        CC_KEEP           => axi_cc_keep,
        CC_VALID          => axi_cc_valid,
        CC_READY          => axi_cc_ready,

        -- Configuration Status Interface
        MAX_PAYLOAD_SIZE  => MAX_PAYLOAD_SIZE,

        -- MI32 interface
        MI_DWR            => mi_dwr,
        MI_ADDR           => mi_addr,
        MI_BE             => mi_be,
        MI_RD             => mi_rd,
        MI_WR             => mi_wr,
        MI_DRD            => mi_drd,
        MI_ARDY           => mi_ardy,
        MI_DRDY           => mi_drdy
    );

    -- =========================================================================
    --  DEBUG REGISTERS
    -- =========================================================================

    mi_ardy <= mi_rd or mi_wr;

    mi_drdy_reg_p : process (clk)
    begin
        if (rising_edge(clk)) then
            if (reset = '1') then
                mi_drdy <= '0';
            else
                mi_drdy <= mi_rd;
            end if;
        end if;
    end process;

    mi_drd_reg_p : process (clk)
    begin
        if (rising_edge(clk)) then
            case(mi_addr(7 downto 0)) is
                when X"00" =>
                    mi_drd <= X"20190520";
                when X"04" =>
                    mi_drd <= s_scratch_reg;
                when X"08" =>
                    mi_drd <= s_control_reg;
                when others =>
                    mi_drd <= X"DEADCAFE";
            end case;
        end if;
    end process;

    s_scratch_reg_sel <= '1' when (mi_addr(7 downto 0) = X"04") else '0';
    s_scratch_reg_we  <= s_scratch_reg_sel and mi_wr;

    scratch_reg_p : process (clk)
    begin
        if (rising_edge(clk)) then
            if (reset = '1') then
                s_scratch_reg <= (others => '0');
            elsif (s_scratch_reg_we = '1') then
                s_scratch_reg <= mi_dwr;
            end if;
        end if;
    end process;

    s_control_reg_sel <= '1' when (mi_addr(7 downto 0) = X"08") else '0';
    s_control_reg_we  <= s_control_reg_sel and mi_wr;

    control_reg_p : process (clk)
    begin
        if (rising_edge(clk)) then
            if (reset = '1') then
                s_control_reg <= (others => '0');
            elsif (s_control_reg_we = '1') then
                s_control_reg <= mi_dwr;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  SIMULATION PROCESS
    -- =========================================================================

    avst_rx_p : process
    begin
        pcie_avst_rx_valid <= (others => '0');
        wait for 2 * RESET_TIME;
        wait for 0.9 * CLK_PERIOD;

        pcie_avst_rx_bar_range <= (others => '0');
        pcie_avst_rx_data(511 downto 128) <= (others => '0');
        pcie_avst_rx_data(127 downto 0) <= SSPL_PCIE_PKT;
        pcie_avst_rx_sop <= "01";
        pcie_avst_rx_eop <= "01";
        pcie_avst_rx_empty(2 downto 0) <= std_logic_vector(to_unsigned(3,3));
        pcie_avst_rx_empty(5 downto 3) <= std_logic_vector(to_unsigned(0,3));
        pcie_avst_rx_valid <= "01";

        wait for CLK_PERIOD;

        pcie_avst_rx_data <= (others => '0');
        pcie_avst_rx_sop <= (others => '0');
        pcie_avst_rx_eop <= (others => '0');
        pcie_avst_rx_empty <= (others => '0');
        pcie_avst_rx_valid <= (others => '0');

        wait for 3*CLK_PERIOD;

        pcie_avst_rx_bar_range <= (others => '0');
        pcie_avst_rx_data(511 downto 128) <= (others => '0');
        pcie_avst_rx_data(127 downto 0) <= WR_PCIE_PKT;
        pcie_avst_rx_sop <= "01";
        pcie_avst_rx_eop <= "01";
        pcie_avst_rx_empty(2 downto 0) <= std_logic_vector(to_unsigned(4,3));
        pcie_avst_rx_empty(5 downto 3) <= std_logic_vector(to_unsigned(0,3));
        pcie_avst_rx_valid <= "01";

        wait for CLK_PERIOD;

        pcie_avst_rx_bar_range <= (others => '0');
        pcie_avst_rx_data(511 downto 128) <= (others => '0');
        pcie_avst_rx_data(127 downto 0) <= RD_PCIE_PKT;
        pcie_avst_rx_sop <= "01";
        pcie_avst_rx_eop <= "01";
        pcie_avst_rx_empty(2 downto 0) <= std_logic_vector(to_unsigned(5,3));
        pcie_avst_rx_empty(5 downto 3) <= std_logic_vector(to_unsigned(0,3));
        pcie_avst_rx_valid <= "01";

        wait for CLK_PERIOD;

        pcie_avst_rx_bar_range <= (others => '0');
        pcie_avst_rx_data(511 downto 384) <= (others => '0');
        pcie_avst_rx_data(383 downto 256) <= WR_PCIE_PKT;
        pcie_avst_rx_data(255 downto 128) <= (others => '0');
        pcie_avst_rx_data(127 downto 0) <= RD_PCIE_PKT;
        pcie_avst_rx_sop <= "11";
        pcie_avst_rx_eop <= "11";
        pcie_avst_rx_empty(2 downto 0) <= std_logic_vector(to_unsigned(5,3));
        pcie_avst_rx_empty(5 downto 3) <= std_logic_vector(to_unsigned(4,3));
        pcie_avst_rx_valid <= "11";

        wait for CLK_PERIOD;

        pcie_avst_rx_bar_range <= (others => '0');
        pcie_avst_rx_data(511 downto 128) <= (others => '0');
        pcie_avst_rx_data(127 downto 0) <= RD_PCIE_PKT;
        pcie_avst_rx_sop <= "01";
        pcie_avst_rx_eop <= "01";
        pcie_avst_rx_empty(2 downto 0) <= std_logic_vector(to_unsigned(5,3));
        pcie_avst_rx_empty(5 downto 3) <= std_logic_vector(to_unsigned(0,3));
        pcie_avst_rx_valid <= "01";

        wait for CLK_PERIOD;

        pcie_avst_rx_data <= (others => '0');
        pcie_avst_rx_sop <= (others => '0');
        pcie_avst_rx_eop <= (others => '0');
        pcie_avst_rx_empty <= (others => '0');
        pcie_avst_rx_valid <= (others => '0');

        wait;
    end process;

end FULL;
