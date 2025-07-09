-- hdr_extract.vhd: AXIS_HDR_EXTRACT component
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity AXIS_HDR_EXTRACT is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH    : natural := 512;
        -- Header offset in bits.
        HDR_START_FIXED    : natural := 0;
        -- Use header offset from port HDR_START.
        HDR_START_EXTERNAL : boolean := false;
        -- Header width in bits.
        HDR_WIDTH          : natural := 112;
        -- Target device.
        DEVICE             : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK                   : in  std_logic;
        RESET                 : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA          : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP          : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST          : in  std_logic;
        RX_AXI_TVALID         : in  std_logic;
        RX_AXI_TREADY         : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA          : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP          : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST          : out std_logic;
        TX_AXI_TVALID         : out std_logic;
        TX_AXI_TREADY         : in  std_logic;

        -- =========================================================================
        -- CONTROL SIGNALS
        -- =========================================================================
        -- Enable signal.
        ENABLE                : in  std_logic;
        -- External header offset.
        HDR_START             : in  std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0) := (others => '0');
        -- External header offset validity indicator.
        HDR_START_VLD         : in  std_logic;
        -- Next header offset.
        HDR_NEXT              : out std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
        -- Next header offset validity indicator.
        HDR_NEXT_VLD          : out std_logic;

        -- =========================================================================
        -- PROTOCOL HEADER
        -- =========================================================================
        -- Header.
        HDR_EXTRACTED         : out std_logic_vector(HDR_WIDTH-1 downto 0);
        -- Header validity indicator.
        HDR_EXTRACTED_VLD     : out std_logic;
        -- Header (registered value).
        HDR_EXTRACTED_REG     : out std_logic_vector(HDR_WIDTH-1 downto 0);
        -- Header (registered value) validity indicator.
        HDR_EXTRACTED_VLD_REG : out std_logic
    );
end entity;

architecture FULL of AXIS_HDR_EXTRACT is

    signal s_enable_reg        : std_logic;

    signal s_tx_axi_tdata      : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_tx_axi_tkeep      : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_tx_axi_tlast      : std_logic;
    signal s_tx_axi_tvalid     : std_logic;
    signal s_tx_axi_tready     : std_logic;

    signal s_hdr_next          : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_hdr_next_vld      : std_logic;
    signal s_hdr_extracted     : std_logic_vector(HDR_WIDTH-1 downto 0);
    signal s_hdr_extracted_vld : std_logic;

begin

    -- To support 100GbE it is sufficient to extract all headers (MAC, VLAN) from first data word (512b).
    -- TODO: add support for different Ethernet standards.
    hdr_start_fixed_g : if not HDR_START_EXTERNAL generate
        constant HDR_END_FIXED : natural := HDR_START_FIXED + HDR_WIDTH;
    begin
        hdr_in_one_transfer_g : if HDR_END_FIXED <= AXI_TDATA_WIDTH generate
            signal s_hdr_vld_simple : std_logic;
        begin
            s_enable_reg          <= ENABLE and HDR_START_VLD;

            s_tx_axi_tdata        <= RX_AXI_TDATA;
            s_tx_axi_tkeep        <= RX_AXI_TKEEP;
            s_tx_axi_tlast        <= RX_AXI_TLAST;
            s_tx_axi_tvalid       <= RX_AXI_TVALID;
            RX_AXI_TREADY         <= s_tx_axi_tready;

            s_hdr_vld_simple      <= not RESET and s_enable_reg;
            s_hdr_next            <= std_logic_vector(to_unsigned(HDR_END_FIXED/8, log2(AXI_TDATA_WIDTH/8)));
            s_hdr_next_vld        <= s_hdr_vld_simple;
            s_hdr_extracted       <= RX_AXI_TDATA(HDR_END_FIXED-1 downto HDR_START_FIXED);
            s_hdr_extracted_vld   <= s_hdr_vld_simple;
        end generate;
    end generate;

    TX_AXI_TDATA      <= s_tx_axi_tdata;
    TX_AXI_TKEEP      <= s_tx_axi_tkeep;
    TX_AXI_TLAST      <= s_tx_axi_tlast;
    TX_AXI_TVALID     <= s_tx_axi_tvalid;
    s_tx_axi_tready   <= TX_AXI_TREADY;

    HDR_NEXT          <= s_hdr_next;
    HDR_NEXT_VLD      <= s_hdr_next_vld;
    HDR_EXTRACTED     <= s_hdr_extracted;
    HDR_EXTRACTED_VLD <= s_hdr_extracted_vld;

    hdr_extracted_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                HDR_EXTRACTED_VLD_REG <= '0';
            elsif (s_enable_reg = '1') then
                HDR_EXTRACTED_REG     <= s_hdr_extracted;
                HDR_EXTRACTED_VLD_REG <= s_hdr_extracted_vld;
            end if;
        end if;
    end process;

end architecture;
