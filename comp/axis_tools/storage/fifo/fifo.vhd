-- fifo.vhd: AXIS_FIFO component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

-- This component acts as a wrapper of common FIFOs adapting them to AXI Stream bus.
entity AXIS_FIFO is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH     : natural := 512;
        -- AXI-Stream destination width in bits (switch purposes only).
        AXI_TUSER_WIDTH     : natural := 0;
        -- Number of items (FIFO depth).
        ITEMS               : natural := 0;
        -- Fake FIFO functionality.
        FAKE_FIFO           : boolean := ITEMS = 0;
        -- See FIFOX.
        RAM_TYPE            : string  := "AUTO";
        -- Target device.
        DEVICE              : string  := "AGILEX";
        -- See FIFOX.
        ALMOST_FULL_OFFSET  : natural := 0;
        -- See FIFOX.
        ALMOST_EMPTY_OFFSET : natural := 0;
        -- Supported are:
        --      0 -> sync registers
        --      1 -> "FIFOX"
        --      2 -> "REG_FIFO"
        FIFO_TYPE           : natural := 0
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- =========================================================================
        -- RX AXI STREAM INTERFACE
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TUSER    : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0) := (others => '0');
        RX_AXI_TLAST    : in  std_logic;
        RX_AXI_TVALID   : in  std_logic;
        RX_AXI_TREADY   : out std_logic;

        -- =========================================================================
        -- TX AXI STREAM INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TUSER    : out std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
        TX_AXI_TLAST    : out std_logic;
        TX_AXI_TVALID   : out std_logic;
        TX_AXI_TREADY   : in  std_logic;

        -- =========================================================================
        -- OPTIONAL STATUS SIGNALS (if supported by the subsequent FIFO component)
        -- =========================================================================
        -- Full indicator.
        FULL            : out std_logic;
        -- Almost full indicator.
        AFULL           : out std_logic;
        -- Currently occupied capacity.
        STATUS          : out std_logic_vector(max(1, log2(ITEMS)) downto 0);
        -- Empty indicator.
        EMPTY           : out std_logic;
        -- Almost empty indicator.
        AEMPTY          : out std_logic
    );
end entity;

architecture FULL of AXIS_FIFO is
    constant FIFO_DATA_WIDTH : natural := 1 + AXI_TUSER_WIDTH + (AXI_TDATA_WIDTH/8) + AXI_TDATA_WIDTH;
    subtype  AXI_TDATA_R     is natural range  AXI_TDATA_WIDTH                           -1 downto 0;
    subtype  AXI_TKEEP_R     is natural range (AXI_TDATA_R'high+1) + (AXI_TDATA_WIDTH/8) -1 downto (AXI_TDATA_R'high+1);

    signal s_rx_axi_ifc_packed : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);
    signal s_tx_axi_ifc_packed : std_logic_vector(FIFO_DATA_WIDTH-1 downto 0);

    signal s_sync_regs_arr     : slv_array_t(ITEMS+1-1 downto 0)(FIFO_DATA_WIDTH+1-1 downto 0);
    signal s_sync_regs_vld_arr : std_logic_vector(ITEMS-1 downto 0);
begin

    axi_tdest_g : if AXI_TUSER_WIDTH > 0 generate
        subtype AXI_TUSER_R is natural range (AXI_TKEEP_R'high+1) + AXI_TUSER_WIDTH -1 downto (AXI_TKEEP_R'high+1);
    begin
        s_rx_axi_ifc_packed <= RX_AXI_TLAST & RX_AXI_TUSER & RX_AXI_TKEEP & RX_AXI_TDATA;
        TX_AXI_TUSER        <= s_tx_axi_ifc_packed(AXI_TUSER_R);
    else generate
        s_rx_axi_ifc_packed <= RX_AXI_TLAST & RX_AXI_TKEEP & RX_AXI_TDATA;
    end generate;

    fifo_comp_g : case FIFO_TYPE generate
        when 0      =>
            s_sync_regs_arr(0) <= RX_AXI_TVALID & s_rx_axi_ifc_packed;
            RX_AXI_TREADY      <= TX_AXI_TREADY;
            sync_regs_g : for i in 1 to ITEMS generate
                sync_regs_p : process (CLK)
                begin
                    if (rising_edge(CLK)) then
                        if (RESET = '1') then
                            s_sync_regs_arr(i)(FIFO_DATA_WIDTH) <= '0';
                        elsif (TX_AXI_TREADY = '1') then
                            s_sync_regs_arr(i) <= s_sync_regs_arr(i-1);
                        end if;
                    end if;
                end process;
                s_sync_regs_vld_arr(i-1) <= s_sync_regs_arr(i)(FIFO_DATA_WIDTH);
            end generate;
            (TX_AXI_TVALID, s_tx_axi_ifc_packed) <= s_sync_regs_arr(ITEMS);
            FULL                                 <= and s_sync_regs_vld_arr;
            EMPTY                                <= nor s_sync_regs_vld_arr;

        when 1      =>
            fifox_i : entity work.FIFOX
            generic map (
                DATA_WIDTH          => FIFO_DATA_WIDTH,
                ITEMS               => ITEMS,
                RAM_TYPE            => RAM_TYPE,
                DEVICE              => DEVICE,
                ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET,
                ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET,
                FAKE_FIFO           => FAKE_FIFO
            )
            port map (
                CLK    => CLK,
                RESET  => RESET,
                DI     => s_rx_axi_ifc_packed,
                WR     => RX_AXI_TVALID,
                FULL   => FULL,
                AFULL  => AFULL,
                STATUS => STATUS,
                DO     => s_tx_axi_ifc_packed,
                RD     => TX_AXI_TREADY,
                EMPTY  => EMPTY,
                AEMPTY => AEMPTY
            );

            RX_AXI_TREADY <= not FULL;
            TX_AXI_TVALID <= not EMPTY;

        when 2      =>
            reg_fifo_i : entity work.REG_FIFO
            generic map (
                DATA_WIDTH => FIFO_DATA_WIDTH,
                ITEMS      => ITEMS,
                FAKE_FIFO  => FAKE_FIFO
            )
            port map (
                CLK        => CLK,
                RST        => RESET,
                RX_DATA    => s_rx_axi_ifc_packed,
                RX_SRC_RDY => RX_AXI_TVALID,
                RX_DST_RDY => RX_AXI_TREADY,
                TX_DATA    => s_tx_axi_ifc_packed,
                TX_SRC_RDY => TX_AXI_TVALID,
                TX_DST_RDY => TX_AXI_TREADY
            );

        when others =>
            s_tx_axi_ifc_packed <= s_rx_axi_ifc_packed;
            RX_AXI_TREADY       <= TX_AXI_TREADY;
            TX_AXI_TVALID       <= RX_AXI_TVALID;

    end generate;

    TX_AXI_TDATA <= s_tx_axi_ifc_packed(AXI_TDATA_R);
    TX_AXI_TKEEP <= s_tx_axi_ifc_packed(AXI_TKEEP_R);
    TX_AXI_TLAST <= s_tx_axi_ifc_packed(s_tx_axi_ifc_packed'high);

end architecture;
