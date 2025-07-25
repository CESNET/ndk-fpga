-- parser.vhd: AXIS_PARSER component
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

use work.proto_hdr_pack.all;

entity AXIS_PARSER is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH : natural := 512;
        -- Target device.
        DEVICE          : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- CLOCK AND RESET
        -- =========================================================================
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- =========================================================================
        -- RX AXI INTERFACE
        -- =========================================================================
        RX_AXI_TDATA    : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP    : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST    : in  std_logic;
        RX_AXI_TVALID   : in  std_logic;
        RX_AXI_TREADY   : out std_logic;

        -- =========================================================================
        -- TX AXI INTERFACE
        -- =========================================================================
        TX_AXI_TDATA    : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP    : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST    : out std_logic;
        TX_AXI_TVALID   : out std_logic;
        TX_AXI_TREADY   : in  std_logic;

        -- =========================================================================
        -- PROTOCOL HEADERS
        -- =========================================================================
        HDR_MAC         : out std_logic_vector(MAC_HDR_W-1 downto 0);
        HDR_MAC_VLD     : out std_logic;
        HDR_VLAN1       : out std_logic_vector(VLAN_HDR_W-1 downto 0);
        HDR_VLAN1_VLD   : out std_logic;
        HDR_VLAN2       : out std_logic_vector(VLAN_HDR_W-1 downto 0);
        HDR_VLAN2_VLD   : out std_logic;
        PAYLOAD_PTR     : out std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);

        -- =========================================================================
        -- CONTROL SIGNALS
        -- =========================================================================
        -- All headers for the current frame parsed.
        HEADERS_SRC_RDY : out std_logic
    );
end entity;

architecture FULL of AXIS_PARSER is

    -- according to MFB2AXI bridge component, AXI communication is always aligned and continuous
    constant AXI_SOF_POS         : natural := 0;
    constant AXI_HDR_START_MAC   : natural := AXI_SOF_POS;
    constant AXI_HDR_START_VLAN1 : natural := AXI_HDR_START_MAC + MAC_HDR_W - MAC_ETHERTYPE_W;
    constant AXI_HDR_END_MAC1    : natural := AXI_HDR_START_VLAN1 + VLAN_HDR_W;
    constant AXI_HDR_START_VLAN2 : natural := AXI_HDR_END_MAC1;
    constant AXI_HDR_END_MAC2    : natural := AXI_HDR_START_VLAN2 + VLAN_HDR_W;

    -- -----
    -- MAC
    -- -----
    signal s_mac_next               : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_mac_next_vld           : std_logic;
    signal s_mac_hdr                : std_logic_vector(MAC_HDR_W-1 downto 0);
    signal s_mac_hdr_vld            : std_logic;

    signal s_mac_eth1_next          : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_mac_eth1_next_vld      : std_logic;
    signal s_mac_eth1               : std_logic_vector(MAC_ETHERTYPE_W-1 downto 0);
    signal s_mac_eth1_vld           : std_logic;

    signal s_mac_eth2_next          : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_mac_eth2_next_vld      : std_logic;
    signal s_mac_eth2               : std_logic_vector(MAC_ETHERTYPE_W-1 downto 0);
    signal s_mac_eth2_vld           : std_logic;

    signal s_mac_hdr_united         : std_logic_vector(MAC_HDR_W-1 downto 0);
    signal s_mac_ethertype          : std_logic_vector(MAC_ETHERTYPE_W-1 downto 0);
    signal s_payload_ptr            : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);

    -- -----
    -- VLAN (802.1q, 802.1ad)
    -- -----
    signal s_vlan1_next             : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_vlan1_next_vld         : std_logic;
    signal s_vlan1_hdr              : std_logic_vector(VLAN_HDR_W-1 downto 0);
    signal s_vlan1_hdr_vld          : std_logic;

    signal s_vlan2_next             : std_logic_vector(log2(AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_vlan2_next_vld         : std_logic;
    signal s_vlan2_hdr              : std_logic_vector(VLAN_HDR_W-1 downto 0);
    signal s_vlan2_hdr_vld          : std_logic;

    signal s_vlan_q_en              : std_logic;
    signal s_vlan_ad_en             : std_logic;
    signal s_vlan_ad_en_2           : std_logic;

    -- -----
    -- AXI interconnect
    -- -----
    signal s_mac_tx_axi_tdata       : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_mac_tx_axi_tkeep       : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_mac_tx_axi_tlast       : std_logic;
    signal s_mac_tx_axi_tvalid      : std_logic;
    signal s_mac_tx_axi_tready      : std_logic;

    signal s_vlan1_tx_axi_tdata     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_vlan1_tx_axi_tkeep     : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_vlan1_tx_axi_tlast     : std_logic;
    signal s_vlan1_tx_axi_tvalid    : std_logic;
    signal s_vlan1_tx_axi_tready    : std_logic;

    signal s_mac_eth1_tx_axi_tdata  : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_mac_eth1_tx_axi_tkeep  : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_mac_eth1_tx_axi_tlast  : std_logic;
    signal s_mac_eth1_tx_axi_tvalid : std_logic;
    signal s_mac_eth1_tx_axi_tready : std_logic;

    signal s_vlan2_tx_axi_tdata     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal s_vlan2_tx_axi_tkeep     : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal s_vlan2_tx_axi_tlast     : std_logic;
    signal s_vlan2_tx_axi_tvalid    : std_logic;
    signal s_vlan2_tx_axi_tready    : std_logic;
    -- -----

    -- auxiliary signals
    signal s_start_of_frame         : std_logic;
    signal s_in_frame_reg           : std_logic;

begin

    s_start_of_frame <= RX_AXI_TVALID and RX_AXI_TREADY and not s_in_frame_reg;
    s_in_frame_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1' or RX_AXI_TLAST = '1') then
                s_in_frame_reg <= '0';
            elsif (s_start_of_frame = '1') then
                s_in_frame_reg <= '1';
            end if;
        end if;
    end process;

    -- TODO: adjust control and data (sync) for < 100GbE
    all_in_one_word_g : if AXI_TDATA_WIDTH >= MAC_HDR_W + 2*VLAN_HDR_W generate
        HDR_MAC         <= s_mac_hdr_united;
        HDR_MAC_VLD     <= s_mac_hdr_vld;
        HDR_VLAN1       <= s_vlan1_hdr;
        HDR_VLAN1_VLD   <= s_vlan1_hdr_vld;
        HDR_VLAN2       <= s_vlan2_hdr;
        HDR_VLAN2_VLD   <= s_vlan2_hdr_vld;
        PAYLOAD_PTR     <= s_payload_ptr;
        HEADERS_SRC_RDY <= s_start_of_frame;
    end generate;

    mac_parser_i : entity work.AXIS_HDR_EXTRACT
    generic map (
        AXI_TDATA_WIDTH       => AXI_TDATA_WIDTH,
        HDR_START_FIXED       => AXI_HDR_START_MAC,
        HDR_START_EXTERNAL    => false,
        HDR_WIDTH             => MAC_HDR_W,
        DEVICE                => DEVICE
    )
    port map (
        CLK                   => CLK,
        RESET                 => RESET,
        RX_AXI_TDATA          => RX_AXI_TDATA,
        RX_AXI_TKEEP          => RX_AXI_TKEEP,
        RX_AXI_TLAST          => RX_AXI_TLAST,
        RX_AXI_TVALID         => RX_AXI_TVALID,
        RX_AXI_TREADY         => RX_AXI_TREADY,
        TX_AXI_TDATA          => s_mac_tx_axi_tdata,
        TX_AXI_TKEEP          => s_mac_tx_axi_tkeep,
        TX_AXI_TLAST          => s_mac_tx_axi_tlast,
        TX_AXI_TVALID         => s_mac_tx_axi_tvalid,
        TX_AXI_TREADY         => s_mac_tx_axi_tready,
        ENABLE                => '1',
        HDR_START             => (others => '0'),
        HDR_START_VLD         => s_start_of_frame,
        HDR_NEXT              => s_mac_next,
        HDR_NEXT_VLD          => s_mac_next_vld,
        HDR_EXTRACTED         => s_mac_hdr,
        HDR_EXTRACTED_VLD     => s_mac_hdr_vld,
        HDR_EXTRACTED_REG     => open,
        HDR_EXTRACTED_VLD_REG => open
    );

    -- TODO: adjust control for < 100GbE
    s_vlan_q_en      <= '1' when s_mac_hdr_vld = '1' and s_mac_hdr(MAC_ETHERTYPE_R) = X"0081" else '0';
    s_vlan_ad_en     <= '1' when s_mac_hdr_vld = '1' and s_mac_hdr(MAC_ETHERTYPE_R) = X"A888" else '0';
    s_vlan_ad_en_2   <= '1' when s_vlan1_hdr_vld = '1' and s_vlan1_hdr(VLAN_TCI_VID_R) = X"0081" else '0';
    s_mac_ethertype  <= s_mac_eth1 when s_mac_eth1_vld = '1' else
                        s_mac_eth2 when s_mac_eth2_vld = '1' else
                        s_mac_hdr(MAC_ETHERTYPE_R);
    s_mac_hdr_united <= s_mac_ethertype & s_mac_hdr(MAC_SRC_R) & s_mac_hdr(MAC_DST_R);
    s_payload_ptr    <= s_mac_eth1_next when s_mac_eth1_next_vld = '1' else
                        s_mac_eth2_next when s_mac_eth2_next_vld = '1' else
                        s_mac_next;

    vlan1_parser_i : entity work.AXIS_HDR_EXTRACT
    generic map (
        AXI_TDATA_WIDTH       => AXI_TDATA_WIDTH,
        HDR_START_FIXED       => AXI_HDR_START_VLAN1,
        HDR_START_EXTERNAL    => false,
        HDR_WIDTH             => VLAN_HDR_W,
        DEVICE                => DEVICE
    )
    port map (
        CLK                   => CLK,
        RESET                 => RESET,
        RX_AXI_TDATA          => s_mac_tx_axi_tdata,
        RX_AXI_TKEEP          => s_mac_tx_axi_tkeep,
        RX_AXI_TLAST          => s_mac_tx_axi_tlast,
        RX_AXI_TVALID         => s_mac_tx_axi_tvalid,
        RX_AXI_TREADY         => s_mac_tx_axi_tready,
        TX_AXI_TDATA          => s_vlan1_tx_axi_tdata,
        TX_AXI_TKEEP          => s_vlan1_tx_axi_tkeep,
        TX_AXI_TLAST          => s_vlan1_tx_axi_tlast,
        TX_AXI_TVALID         => s_vlan1_tx_axi_tvalid,
        TX_AXI_TREADY         => s_vlan1_tx_axi_tready,
        ENABLE                => s_vlan_q_en or s_vlan_ad_en,
        HDR_START             => s_mac_next,
        HDR_START_VLD         => s_mac_next_vld,
        HDR_NEXT              => s_vlan1_next,
        HDR_NEXT_VLD          => s_vlan1_next_vld,
        HDR_EXTRACTED         => s_vlan1_hdr,
        HDR_EXTRACTED_VLD     => s_vlan1_hdr_vld,
        HDR_EXTRACTED_REG     => open,
        HDR_EXTRACTED_VLD_REG => open
    );

    mac_ethertype1_parser_i : entity work.AXIS_HDR_EXTRACT
    generic map (
        AXI_TDATA_WIDTH       => AXI_TDATA_WIDTH,
        HDR_START_FIXED       => AXI_HDR_END_MAC1,
        HDR_START_EXTERNAL    => false,
        HDR_WIDTH             => MAC_ETHERTYPE_W,
        DEVICE                => DEVICE
    )
    port map (
        CLK                   => CLK,
        RESET                 => RESET,
        RX_AXI_TDATA          => s_vlan1_tx_axi_tdata,
        RX_AXI_TKEEP          => s_vlan1_tx_axi_tkeep,
        RX_AXI_TLAST          => s_vlan1_tx_axi_tlast,
        RX_AXI_TVALID         => s_vlan1_tx_axi_tvalid,
        RX_AXI_TREADY         => s_vlan1_tx_axi_tready,
        TX_AXI_TDATA          => s_mac_eth1_tx_axi_tdata,
        TX_AXI_TKEEP          => s_mac_eth1_tx_axi_tkeep,
        TX_AXI_TLAST          => s_mac_eth1_tx_axi_tlast,
        TX_AXI_TVALID         => s_mac_eth1_tx_axi_tvalid,
        TX_AXI_TREADY         => s_mac_eth1_tx_axi_tready,
        ENABLE                => s_vlan_q_en,
        HDR_START             => s_vlan1_next,
        HDR_START_VLD         => s_vlan1_next_vld,
        HDR_NEXT              => s_mac_eth1_next,
        HDR_NEXT_VLD          => s_mac_eth1_next_vld,
        HDR_EXTRACTED         => s_mac_eth1,
        HDR_EXTRACTED_VLD     => s_mac_eth1_vld,
        HDR_EXTRACTED_REG     => open,
        HDR_EXTRACTED_VLD_REG => open
    );

    vlan2_parser_i : entity work.AXIS_HDR_EXTRACT
    generic map (
        AXI_TDATA_WIDTH       => AXI_TDATA_WIDTH,
        HDR_START_FIXED       => AXI_HDR_START_VLAN2,
        HDR_START_EXTERNAL    => false,
        HDR_WIDTH             => VLAN_HDR_W,
        DEVICE                => DEVICE
    )
    port map (
        CLK                   => CLK,
        RESET                 => RESET,
        RX_AXI_TDATA          => s_mac_eth1_tx_axi_tdata,
        RX_AXI_TKEEP          => s_mac_eth1_tx_axi_tkeep,
        RX_AXI_TLAST          => s_mac_eth1_tx_axi_tlast,
        RX_AXI_TVALID         => s_mac_eth1_tx_axi_tvalid,
        RX_AXI_TREADY         => s_mac_eth1_tx_axi_tready,
        TX_AXI_TDATA          => s_vlan2_tx_axi_tdata,
        TX_AXI_TKEEP          => s_vlan2_tx_axi_tkeep,
        TX_AXI_TLAST          => s_vlan2_tx_axi_tlast,
        TX_AXI_TVALID         => s_vlan2_tx_axi_tvalid,
        TX_AXI_TREADY         => s_vlan2_tx_axi_tready,
        ENABLE                => s_vlan_ad_en_2,
        HDR_START             => s_vlan1_next,
        HDR_START_VLD         => s_vlan1_next_vld,
        HDR_NEXT              => s_vlan2_next,
        HDR_NEXT_VLD          => s_vlan2_next_vld,
        HDR_EXTRACTED         => s_vlan2_hdr,
        HDR_EXTRACTED_VLD     => s_vlan2_hdr_vld,
        HDR_EXTRACTED_REG     => open,
        HDR_EXTRACTED_VLD_REG => open
    );

    mac_ethertype2_parser_i : entity work.AXIS_HDR_EXTRACT
    generic map (
        AXI_TDATA_WIDTH       => AXI_TDATA_WIDTH,
        HDR_START_FIXED       => AXI_HDR_END_MAC2,
        HDR_START_EXTERNAL    => false,
        HDR_WIDTH             => MAC_ETHERTYPE_W,
        DEVICE                => DEVICE
    )
    port map (
        CLK                   => CLK,
        RESET                 => RESET,
        RX_AXI_TDATA          => s_vlan2_tx_axi_tdata,
        RX_AXI_TKEEP          => s_vlan2_tx_axi_tkeep,
        RX_AXI_TLAST          => s_vlan2_tx_axi_tlast,
        RX_AXI_TVALID         => s_vlan2_tx_axi_tvalid,
        RX_AXI_TREADY         => s_vlan2_tx_axi_tready,
        TX_AXI_TDATA          => TX_AXI_TDATA,
        TX_AXI_TKEEP          => TX_AXI_TKEEP,
        TX_AXI_TLAST          => TX_AXI_TLAST,
        TX_AXI_TVALID         => TX_AXI_TVALID,
        TX_AXI_TREADY         => TX_AXI_TREADY,
        ENABLE                => s_vlan_ad_en_2,
        HDR_START             => s_vlan2_next,
        HDR_START_VLD         => s_vlan2_next_vld,
        HDR_NEXT              => s_mac_eth2_next,
        HDR_NEXT_VLD          => s_mac_eth2_next_vld,
        HDR_EXTRACTED         => s_mac_eth2,
        HDR_EXTRACTED_VLD     => s_mac_eth2_vld,
        HDR_EXTRACTED_REG     => open,
        HDR_EXTRACTED_VLD_REG => open
    );

end architecture;
