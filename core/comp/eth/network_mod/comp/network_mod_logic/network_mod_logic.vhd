-- network_mod_logic.vhd: this is the component with TX and RX MAC lites, a splitter and a merger.
--                        There is also the MI splitter, maybe Async reset ??
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;

entity NETWORK_MOD_LOGIC is
generic(
    -- =====================================================================
    -- Ethernet configuration:
    -- =====================================================================
    -- Number ETH streams per ETH port, must be equal to 1 or ETH_PORT_CHAN!
    ETH_STREAMS     : natural := 1;
    -- Select number of channels per Ethernet port.
    -- Options: 400G1            card: 1, 2, 4, 8;
    --          DK-DEV-AGI027RES card: 1, 2, 4, 8;
    --          DK-DEV-1SDX-P    card: 1, 4.
    ETH_PORT_CHAN   : natural := 4;
    -- Different port ID for each Ethernet port (for RX MAC Lite identification)
    ETH_PORT_ID     : natural := 0;
    -- Maximum allowed size of RX frame in bytes
    ETH_PORT_RX_MTU : natural := 16383;
    -- Maximum allowed size of TX frame in bytes
    ETH_PORT_TX_MTU : natural := 16383;
    -- Optional option to disable MAC Lite modules. Dangerously!
    ETH_MAC_BYPASS : boolean := False;

    -- =====================================================================
    -- MFB configuration:
    -- =====================================================================
    -- USER side (2x wider than CORE side)
    USER_REGIONS      : natural := 2;
    USER_REGION_SIZE  : natural := 8;

    -- CORE side
    CORE_REGIONS      : natural := 1;
    CORE_REGION_SIZE  : natural := 8;

    -- COMMON for both sides
    BLOCK_SIZE        : natural := 8; -- other values than 8 are not supported
    ITEM_WIDTH        : natural := 8; -- other values than 8 are not supported

    -- =====================================================================
    -- MI configuration:
    -- =====================================================================
    MI_DATA_WIDTH     : natural := 32;
    MI_ADDR_WIDTH     : natural := 32;

    -- =====================================================================
    -- OTHER configuration:
    -- =====================================================================
    RESET_USER_WIDTH  : natural := 8;
    --                             ETH_PORT_CHAN x (TX MAC lite + RX MAC lite)
    RESET_CORE_WIDTH  : natural := ETH_PORT_CHAN * (1           + 1          );
    -- Resize Buffer feature of RX_MAC_LITE.
    RESIZE_BUFFER     : boolean := True;
    -- Select FPGA device.
    DEVICE            : string := "STRATIX10"; -- AGILEX, STRATIX10, ULTRASCALE
    -- Select target board. Unused, only for back-compatibility.
    BOARD             : string := "DK-DEV-1SDX-P" -- 400G1, DK-DEV-AGI027RES, DK-DEV-1SDX-P
);
port(
    -- =====================================================================
    -- CLOCK AND RESET
    -- =====================================================================
    CLK_USER        : in std_logic;
    CLK_CORE        : in std_logic;

    RESET_USER      : in std_logic_vector(RESET_USER_WIDTH-1 downto 0);
    RESET_CORE      : in std_logic_vector(RESET_CORE_WIDTH-1 downto 0);

    -- Status/control interface
    ACTIVITY_RX     : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    ACTIVITY_TX     : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    RX_LINK_UP      : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    TX_LINK_UP      : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- =====================================================================
    -- USER interface
    -- =====================================================================
    -- from the USER
    RX_USER_MFB_DATA     : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*USER_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_USER_MFB_HDR      : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*ETH_TX_HDR_WIDTH-1 downto 0); -- valid with SOF
    RX_USER_MFB_SOF_POS  : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*max(1,log2(USER_REGION_SIZE))-1 downto 0);
    RX_USER_MFB_EOF_POS  : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*max(1,log2(USER_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_USER_MFB_SOF      : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS-1 downto 0);
    RX_USER_MFB_EOF      : in  slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS-1 downto 0);
    RX_USER_MFB_SRC_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);
    RX_USER_MFB_DST_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);

    -- to the USER
    TX_USER_MFB_DATA     : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*USER_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_USER_MFB_SOF_POS  : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*max(1,log2(USER_REGION_SIZE))-1 downto 0);
    TX_USER_MFB_EOF_POS  : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*max(1,log2(USER_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_USER_MFB_SOF      : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS-1 downto 0);
    TX_USER_MFB_EOF      : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS-1 downto 0);
    TX_USER_MFB_SRC_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);
    TX_USER_MFB_DST_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    TX_USER_MVB_DATA     : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    TX_USER_MVB_VLD      : out slv_array_t     (ETH_STREAMS-1 downto 0)(USER_REGIONS-1 downto 0);
    TX_USER_MVB_SRC_RDY  : out std_logic_vector(ETH_STREAMS-1 downto 0);
    TX_USER_MVB_DST_RDY  : in  std_logic_vector(ETH_STREAMS-1 downto 0);

    -- =====================================================================
    -- CORE interface
    -- =====================================================================
    -- from the CORE
    RX_CORE_MFB_DATA     : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*CORE_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    RX_CORE_MFB_SOF_POS  : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*max(1,log2(CORE_REGION_SIZE))-1 downto 0);
    RX_CORE_MFB_EOF_POS  : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*max(1,log2(CORE_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    RX_CORE_MFB_SOF      : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS-1 downto 0);
    RX_CORE_MFB_EOF      : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS-1 downto 0);
    RX_CORE_MFB_ERROR    : in  slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS-1 downto 0);
    RX_CORE_MFB_SRC_RDY  : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- to the CORE
    TX_CORE_MFB_DATA     : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*CORE_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    TX_CORE_MFB_SOF_POS  : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*max(1,log2(CORE_REGION_SIZE))-1 downto 0);
    TX_CORE_MFB_EOF_POS  : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS*max(1,log2(CORE_REGION_SIZE*BLOCK_SIZE))-1 downto 0);
    TX_CORE_MFB_SOF      : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS-1 downto 0);
    TX_CORE_MFB_EOF      : out slv_array_t     (ETH_PORT_CHAN-1 downto 0)(CORE_REGIONS-1 downto 0);
    TX_CORE_MFB_SRC_RDY  : out std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    TX_CORE_MFB_DST_RDY  : in  std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- =====================================================================
    -- MI interface
    -- =====================================================================
    MI_CLK          : in  std_logic;
    MI_RESET        : in  std_logic;
    MI_DWR          : in  std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ADDR         : in  std_logic_vector(MI_ADDR_WIDTH-1 downto 0);
    MI_RD           : in  std_logic;
    MI_WR           : in  std_logic;
    MI_BE           : in  std_logic_vector(MI_DATA_WIDTH/8-1 downto 0);
    MI_DRD          : out std_logic_vector(MI_DATA_WIDTH-1 downto 0);
    MI_ARDY         : out std_logic;
    MI_DRDY         : out std_logic;

    -- =====================================================================
    -- TSU interface
    -- =====================================================================
    TSU_TS_NS       : in  std_logic_vector(64-1 downto 0);
    TSU_TS_DV       : in  std_logic
);
end entity;

architecture FULL of NETWORK_MOD_LOGIC is

    -- =========================================================================
    --                           FUNCTION declarations
    -- =========================================================================

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================
                                        -- MFB splitter + MFB merger + ETH_PORT_CHAN x (TX MAC lite + RX MAC lite)
    -- constant RESET_CORE_WIDTH   : natural := 1            + 1          + ETH_PORT_CHAN * (1           + 1          );

    constant TX_RX_MAC_OFF  : std_logic_vector(MI_ADDR_WIDTH-1 downto 0) := X"0000_0200";
    constant CHAN_OFF       : std_logic_vector(MI_ADDR_WIDTH-1 downto 0) := X"0000_0400";

    constant MI_ADDR_BASES     : natural := ETH_PORT_CHAN*2;

    -- MFB simplifications
    constant MFB_WIDTH      : natural := USER_REGIONS*USER_REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant MFB_SOFP_WIDTH : natural := USER_REGIONS*max(1,log2(USER_REGION_SIZE));
    constant MFB_EOFP_WIDTH : natural := USER_REGIONS*max(1,log2(USER_REGION_SIZE*BLOCK_SIZE));

    -- =========================================================================
    --                                FUNCTIONS
    -- =========================================================================
    function mi_addr_base_init_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    begin
        for ch in 0 to ETH_PORT_CHAN-1 loop
            for d in 0 to 1 loop -- TX RX direction loop (d=0 -> TX, d=1 -> RX)
                mi_addr_base_var(ch*2 + d) := std_logic_vector(resize(ch*unsigned(CHAN_OFF) +                      -- specify channel
                                                                      d *unsigned(TX_RX_MAC_OFF), MI_ADDR_WIDTH)); -- specify TX/RX
            end loop;
        end loop;
        return mi_addr_base_var;
    end function;

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================

    -- MFB splitter RX (SEL input signals)t
    signal mfb_hdr_arr         : slv_array_t     (USER_REGIONS-1 downto 0)(ETH_TX_HDR_WIDTH          -1 downto 0);
    signal eth_hdr_tx_port_arr : slv_array_t     (USER_REGIONS-1 downto 0)(ETH_TX_HDR_PORT_W         -1 downto 0);
    signal split_addr_arr      : slv_array_t     (USER_REGIONS-1 downto 0)(max(1,log2(ETH_PORT_CHAN))-1 downto 0);
    signal split_addr          : std_logic_vector(USER_REGIONS*            max(1,log2(ETH_PORT_CHAN))-1 downto 0);

    -- From MFB Splitter to TX MAC lite(s)
    signal split_mfb_data    : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_WIDTH-1 downto 0);
    signal split_mfb_sof_pos : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_SOFP_WIDTH-1 downto 0);
    signal split_mfb_eof_pos : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_EOFP_WIDTH-1 downto 0);
    signal split_mfb_sof     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS-1 downto 0);
    signal split_mfb_eof     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS-1 downto 0);
    signal split_mfb_src_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal split_mfb_dst_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- From RX MAC lite to MFB Merger
    -- MFB signals
    signal merg_mfb_data    : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_WIDTH-1 downto 0);
    signal merg_mfb_sof_pos : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_SOFP_WIDTH-1 downto 0);
    signal merg_mfb_eof_pos : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(MFB_EOFP_WIDTH-1 downto 0);
    signal merg_mfb_sof     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS-1 downto 0);
    signal merg_mfb_eof     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS-1 downto 0);
    signal merg_mfb_src_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal merg_mfb_dst_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    -- MVB signals
    signal merg_mvb_data    : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal merg_mvb_vld     : slv_array_t     (ETH_PORT_CHAN-1 downto 0)(USER_REGIONS-1 downto 0);
    signal merg_mvb_src_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);
    signal merg_mvb_dst_rdy : std_logic_vector(ETH_PORT_CHAN-1 downto 0);

    -- MI for MAC lites
    signal mi_split_dwr  : slv_array_t     (ETH_PORT_CHAN*2-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_split_addr : slv_array_t     (ETH_PORT_CHAN*2-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal mi_split_be   : slv_array_t     (ETH_PORT_CHAN*2-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal mi_split_rd   : std_logic_vector(ETH_PORT_CHAN*2-1 downto 0);
    signal mi_split_wr   : std_logic_vector(ETH_PORT_CHAN*2-1 downto 0);
    signal mi_split_ardy : std_logic_vector(ETH_PORT_CHAN*2-1 downto 0);
    signal mi_split_drd  : slv_array_t     (ETH_PORT_CHAN*2-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_split_drdy : std_logic_vector(ETH_PORT_CHAN*2-1 downto 0);

begin

    assert (ETH_STREAMS = ETH_PORT_CHAN or ETH_STREAMS = 1) 
        report "NETWORK_MOD_LOGIC: ETH_STREAMS must be equal to 1 or ETH_PORT_CHAN!" 
        severity failure;

    assert ((ETH_STREAMS = ETH_PORT_CHAN and ETH_MAC_BYPASS = True) or (ETH_MAC_BYPASS = False)) 
        report "NETWORK_MOD_LOGIC: ETH_MAC_BYPASS is supported only when ETH_STREAMS = ETH_PORT_CHAN!" 
        severity failure;

    mi_splitter_g: if not ETH_MAC_BYPASS generate
        -- MI SPLITTER for MAC lites
        mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH  => MI_ADDR_WIDTH      ,
            DATA_WIDTH  => MI_DATA_WIDTH      ,
            META_WIDTH  => 0                  ,
            PORTS       => MI_ADDR_BASES      ,
            PIPE_OUT    => (others => true)   ,
            PIPE_TYPE   => "REG"              ,
            ADDR_BASES  => MI_ADDR_BASES      ,
            ADDR_BASE   => mi_addr_base_init_f,
            DEVICE      => DEVICE
        )
        port map(
            CLK         => MI_CLK  ,
            RESET       => MI_RESET,

            RX_DWR      => MI_DWR         ,
            RX_MWR      => (others => '0'),
            RX_ADDR     => MI_ADDR        ,
            RX_BE       => MI_BE          ,
            RX_RD       => MI_RD          ,
            RX_WR       => MI_WR          ,
            RX_ARDY     => MI_ARDY        ,
            RX_DRD      => MI_DRD         ,
            RX_DRDY     => MI_DRDY        ,
            
            TX_DWR     => mi_split_dwr    ,
            TX_MWR     => open            ,
            TX_ADDR    => mi_split_addr   ,
            TX_BE      => mi_split_be     ,
            TX_RD      => mi_split_rd     ,
            TX_WR      => mi_split_wr     ,
            TX_ARDY    => mi_split_ardy   ,
            TX_DRD     => mi_split_drd    ,
            TX_DRDY    => mi_split_drdy
        );
    else generate
        MI_ARDY <= MI_RD or MI_WR;
        MI_DRDY <= MI_RD;
        MI_DRD  <= X"DEADCAFE"; 
    end generate;

    -- =========================================================================
    -- TX path
    -- =========================================================================

    mfb_splitter_g: if (ETH_STREAMS = 1) generate
        mfb_hdr_arr <= slv_array_downto_deser(RX_USER_MFB_HDR(0), USER_REGIONS);
        splitter_addr_g : for r in USER_REGIONS-1 downto 0 generate
            eth_hdr_tx_port_arr(r) <= mfb_hdr_arr        (r)(ETH_TX_HDR_PORT); -- (8 bits wide)
            split_addr_arr     (r) <= eth_hdr_tx_port_arr(r)(max(1,log2(ETH_PORT_CHAN))-1 downto 0);
        end generate;
        split_addr <= slv_array_ser(split_addr_arr);
    
        -- Split one ETH_STREAM into ETH_CHANNELS for each TX MAC Lite
        mfb_splitter_tree_i : entity work.MFB_SPLITTER_SIMPLE_GEN
        generic map(
            SPLITTER_OUTPUTS => ETH_PORT_CHAN   ,
            REGIONS          => USER_REGIONS    ,
            REGION_SIZE      => USER_REGION_SIZE,
            BLOCK_SIZE       => BLOCK_SIZE      ,
            ITEM_WIDTH       => ITEM_WIDTH      ,
            META_WIDTH       => 0
        )
        port map(
            CLK             => CLK_USER     ,
            RESET           => RESET_USER(0),

            RX_MFB_SEL      => split_addr         ,
            RX_MFB_DATA     => RX_USER_MFB_DATA(0)   ,
            RX_MFB_META     => (others => '0')    ,
            RX_MFB_SOF      => RX_USER_MFB_SOF(0)    ,
            RX_MFB_EOF      => RX_USER_MFB_EOF(0)    ,
            RX_MFB_SOF_POS  => RX_USER_MFB_SOF_POS(0),
            RX_MFB_EOF_POS  => RX_USER_MFB_EOF_POS(0),
            RX_MFB_SRC_RDY  => RX_USER_MFB_SRC_RDY(0),
            RX_MFB_DST_RDY  => RX_USER_MFB_DST_RDY(0),

            TX_MFB_DATA     => split_mfb_data   ,
            TX_MFB_META     => open             ,
            TX_MFB_SOF      => split_mfb_sof    ,
            TX_MFB_EOF      => split_mfb_eof    ,
            TX_MFB_SOF_POS  => split_mfb_sof_pos,
            TX_MFB_EOF_POS  => split_mfb_eof_pos,
            TX_MFB_SRC_RDY  => split_mfb_src_rdy,
            TX_MFB_DST_RDY  => split_mfb_dst_rdy
        );
    else generate
        -- one ETH stream = one ETH channel
        split_mfb_data      <= RX_USER_MFB_DATA;
        split_mfb_sof       <= RX_USER_MFB_SOF;
        split_mfb_eof       <= RX_USER_MFB_EOF;
        split_mfb_sof_pos   <= RX_USER_MFB_SOF_POS;
        split_mfb_eof_pos   <= RX_USER_MFB_EOF_POS;
        split_mfb_src_rdy   <= RX_USER_MFB_SRC_RDY;
        RX_USER_MFB_DST_RDY <= split_mfb_dst_rdy;
    end generate;

    tx_g : for ch in 0 to ETH_PORT_CHAN-1 generate
        tx_mac_g: if not ETH_MAC_BYPASS generate
            tx_mac_i : entity work.TX_MAC_LITE
            generic map(
                RX_REGIONS      => USER_REGIONS    ,
                RX_REGION_SIZE  => USER_REGION_SIZE,
                RX_BLOCK_SIZE   => BLOCK_SIZE      ,
                RX_ITEM_WIDTH   => ITEM_WIDTH      ,
                TX_REGIONS      => CORE_REGIONS    ,
                TX_REGION_SIZE  => CORE_REGION_SIZE,
                TX_BLOCK_SIZE   => BLOCK_SIZE      ,
                TX_ITEM_WIDTH   => ITEM_WIDTH      ,
                RESIZE_ON_TX    => True            ,
                PKT_MTU_BYTES   => ETH_PORT_TX_MTU ,
                RX_INCLUDE_CRC  => false           ,
                RX_INCLUDE_IPG  => false           ,
                CRC_INSERT_EN   => false           ,
                IPG_GENERATE_EN => false           ,
                USE_DSP_CNT     => true            ,
                DEVICE          => DEVICE
            )
            port map(
                MI_CLK         => MI_CLK  ,
                MI_RESET       => MI_RESET,
                MI_DWR         => mi_split_dwr (ch*2+0),
                MI_ADDR        => mi_split_addr(ch*2+0),
                MI_RD          => mi_split_rd  (ch*2+0),
                MI_WR          => mi_split_wr  (ch*2+0),
                MI_BE          => mi_split_be  (ch*2+0),
                MI_DRD         => mi_split_drd (ch*2+0),
                MI_ARDY        => mi_split_ardy(ch*2+0),
                MI_DRDY        => mi_split_drdy(ch*2+0),

                RX_CLK         => CLK_USER             ,
                RX_CLK_X2      => CLK_USER             , -- CX inside is not used, else use CLK_X2
                RX_RESET       => RESET_USER(0)        ,
                RX_MFB_DATA    => split_mfb_data   (ch),
                RX_MFB_SOF_POS => split_mfb_sof_pos(ch),
                RX_MFB_EOF_POS => split_mfb_eof_pos(ch),
                RX_MFB_SOF     => split_mfb_sof    (ch),
                RX_MFB_EOF     => split_mfb_eof    (ch),
                RX_MFB_SRC_RDY => split_mfb_src_rdy(ch),
                RX_MFB_DST_RDY => split_mfb_dst_rdy(ch),

                TX_CLK         => CLK_CORE               ,
                TX_RESET       => RESET_CORE(ch*2)       ,
                TX_MFB_DATA    => TX_CORE_MFB_DATA   (ch),
                TX_MFB_SOF     => TX_CORE_MFB_SOF    (ch),
                TX_MFB_EOF     => TX_CORE_MFB_EOF    (ch),
                TX_MFB_SOF_POS => TX_CORE_MFB_SOF_POS(ch),
                TX_MFB_EOF_POS => TX_CORE_MFB_EOF_POS(ch),
                TX_MFB_SRC_RDY => TX_CORE_MFB_SRC_RDY(ch),
                TX_MFB_DST_RDY => TX_CORE_MFB_DST_RDY(ch),

                OUTGOING_FRAME => ACTIVITY_TX(ch)
            );
        else generate
            -- The MFB bus does not support idles inside frame and runs directly
            -- on the ETH CORE clock.

            TX_CORE_MFB_DATA(ch)    <= split_mfb_data(ch);
            TX_CORE_MFB_SOF(ch)     <= split_mfb_sof(ch);
            TX_CORE_MFB_EOF(ch)     <= split_mfb_eof(ch);
            TX_CORE_MFB_SOF_POS(ch) <= split_mfb_sof_pos(ch);
            TX_CORE_MFB_EOF_POS(ch) <= split_mfb_eof_pos(ch);
            TX_CORE_MFB_SRC_RDY(ch) <= split_mfb_src_rdy(ch);
            split_mfb_dst_rdy(ch)   <= TX_CORE_MFB_DST_RDY(ch);

            ACTIVITY_TX(ch) <= split_mfb_src_rdy(ch) and (or split_mfb_eof(ch));
        end generate;
    end generate;

    -- =========================================================================
    -- RX path
    -- =========================================================================

    rx_g : for ch in 0 to ETH_PORT_CHAN-1 generate
        signal rx_core_mfb_sof_tmp  : std_logic_vector(CORE_REGIONS-1 downto 0);
        signal rx_core_mfb_eof_tmp  : std_logic_vector(CORE_REGIONS-1 downto 0);
    begin
        process(all)
        begin
            -- this fix bug in questasim elsewhere it could be connected directly
            rx_core_mfb_sof_tmp <= RX_CORE_MFB_SOF(ch);
            rx_core_mfb_eof_tmp <= RX_CORE_MFB_EOF(ch);
        end process;

        rx_mac_g: if not ETH_MAC_BYPASS generate
            rx_mac_i : entity work.RX_MAC_LITE
            generic map(
                RX_REGIONS      => CORE_REGIONS    ,
                RX_REGION_SIZE  => CORE_REGION_SIZE,
                RX_BLOCK_SIZE   => BLOCK_SIZE      ,
                RX_ITEM_WIDTH   => ITEM_WIDTH      ,
                TX_REGIONS      => USER_REGIONS    ,
                TX_REGION_SIZE  => USER_REGION_SIZE,
                TX_BLOCK_SIZE   => BLOCK_SIZE      ,
                TX_ITEM_WIDTH   => ITEM_WIDTH      ,
                RESIZE_BUFFER   => RESIZE_BUFFER   ,
                NETWORK_PORT_ID => ETH_PORT_ID*ETH_PORT_CHAN+ch, -- no support different number of channels for each port
                PKT_MTU_BYTES   => ETH_PORT_RX_MTU ,
                CRC_IS_RECEIVED => false           ,
                CRC_CHECK_EN    => false           ,
                CRC_REMOVE_EN   => false           ,
                MAC_CHECK_EN    => true            ,
                MAC_COUNT       => 16              ,
                TIMESTAMP_EN    => true            ,
                DEVICE          => DEVICE
            )
            port map(
                RX_CLK          => CLK_CORE     ,
                RX_RESET        => RESET_CORE(ch*2+1), -- todo
                TX_CLK          => CLK_USER     ,
                TX_RESET        => RESET_USER(0),

                RX_MFB_DATA     => RX_CORE_MFB_DATA   (ch),
                RX_MFB_SOF      => rx_core_mfb_sof_tmp,
                RX_MFB_EOF      => rx_core_mfb_eof_tmp,
                RX_MFB_SOF_POS  => RX_CORE_MFB_SOF_POS(ch),
                RX_MFB_EOF_POS  => RX_CORE_MFB_EOF_POS(ch),
                RX_MFB_ERROR    => RX_CORE_MFB_ERROR  (ch),
                RX_MFB_SRC_RDY  => RX_CORE_MFB_SRC_RDY(ch),

                ADAPTER_LINK_UP => RX_LINK_UP(ch),

                TSU_TS_NS       => TSU_TS_NS,
                TSU_TS_DV       => TSU_TS_DV,

                TX_MFB_DATA     => merg_mfb_data   (ch),
                TX_MFB_SOF      => merg_mfb_sof    (ch),
                TX_MFB_EOF      => merg_mfb_eof    (ch),
                TX_MFB_SOF_POS  => merg_mfb_sof_pos(ch),
                TX_MFB_EOF_POS  => merg_mfb_eof_pos(ch),
                TX_MFB_SRC_RDY  => merg_mfb_src_rdy(ch),
                TX_MFB_DST_RDY  => merg_mfb_dst_rdy(ch),
                TX_MVB_DATA     => merg_mvb_data   (ch),
                TX_MVB_VLD      => merg_mvb_vld    (ch),
                TX_MVB_SRC_RDY  => merg_mvb_src_rdy(ch),
                TX_MVB_DST_RDY  => merg_mvb_dst_rdy(ch),

                LINK_UP         => open,
                INCOMING_FRAME  => ACTIVITY_RX(ch),

                MI_CLK          => MI_CLK  ,
                MI_RESET        => MI_RESET,
                MI_DWR          => mi_split_dwr (ch*2+1),
                MI_ADDR         => mi_split_addr(ch*2+1),
                MI_RD           => mi_split_rd  (ch*2+1),
                MI_WR           => mi_split_wr  (ch*2+1),
                MI_BE           => mi_split_be  (ch*2+1),
                MI_DRD          => mi_split_drd (ch*2+1),
                MI_ARDY         => mi_split_ardy(ch*2+1),
                MI_DRDY         => mi_split_drdy(ch*2+1)
            );
        else generate
            -- The MFB bus does not support DST_RDY and runs directly on the
            -- ETH CORE clock.
            merg_mfb_data(ch)    <= RX_CORE_MFB_DATA(ch);
            merg_mfb_sof(ch)     <= rx_core_mfb_sof_tmp;
            merg_mfb_eof(ch)     <= rx_core_mfb_eof_tmp;
            merg_mfb_sof_pos(ch) <= RX_CORE_MFB_SOF_POS(ch);
            merg_mfb_eof_pos(ch) <= RX_CORE_MFB_EOF_POS(ch);
            merg_mfb_src_rdy(ch) <= RX_CORE_MFB_SRC_RDY(ch);

            -- MVB metadata bus is not supported in this mode.
            merg_mvb_data(ch)    <= (others => '0');
            merg_mvb_vld(ch)     <= (others => '0');
            merg_mvb_src_rdy(ch) <= '0';

            ACTIVITY_RX(ch) <= RX_CORE_MFB_SRC_RDY(ch) and (or rx_core_mfb_eof_tmp);
        end generate;
    end generate;

    mfb_merger_g: if (ETH_STREAMS = 1) generate
        -- Merge all ETH_CHANNELS into one ETH_STREAM from each RX MAC Lite
        mfb_merger_tree_i : entity work.MFB_MERGER_GEN
        generic map(
            MERGER_INPUTS   => ETH_PORT_CHAN   ,
            MVB_ITEMS       => USER_REGIONS    ,
            MVB_ITEM_WIDTH  => ETH_RX_HDR_WIDTH,
            MFB_REGIONS     => USER_REGIONS    ,
            MFB_REG_SIZE    => USER_REGION_SIZE,
            MFB_BLOCK_SIZE  => BLOCK_SIZE      ,
            MFB_ITEM_WIDTH  => ITEM_WIDTH      ,
            INPUT_FIFO_SIZE => 8               ,
            RX_PAYLOAD_EN   => (others => true),
            IN_PIPE_EN      => true            ,
            OUT_PIPE_EN     => true            ,
            DEVICE          => DEVICE
        )
        port map(
            CLK             => CLK_USER        ,
            RESET           => RESET_USER(0)   ,

            RX_MFB_DATA     => merg_mfb_data   ,
            RX_MFB_SOF      => merg_mfb_sof    ,
            RX_MFB_EOF      => merg_mfb_eof    ,
            RX_MFB_SOF_POS  => merg_mfb_sof_pos,
            RX_MFB_EOF_POS  => merg_mfb_eof_pos,
            RX_MFB_SRC_RDY  => merg_mfb_src_rdy,
            RX_MFB_DST_RDY  => merg_mfb_dst_rdy,

            RX_MVB_DATA     => merg_mvb_data   ,
            RX_MVB_PAYLOAD  => (others => (others => '1')),
            RX_MVB_VLD      => merg_mvb_vld    ,
            RX_MVB_SRC_RDY  => merg_mvb_src_rdy,
            RX_MVB_DST_RDY  => merg_mvb_dst_rdy,

            TX_MFB_DATA     => TX_USER_MFB_DATA(0)   ,
            TX_MFB_SOF      => TX_USER_MFB_SOF(0)    ,
            TX_MFB_EOF      => TX_USER_MFB_EOF(0)    ,
            TX_MFB_SOF_POS  => TX_USER_MFB_SOF_POS(0),
            TX_MFB_EOF_POS  => TX_USER_MFB_EOF_POS(0),
            TX_MFB_SRC_RDY  => TX_USER_MFB_SRC_RDY(0),
            TX_MFB_DST_RDY  => TX_USER_MFB_DST_RDY(0),

            TX_MVB_DATA     => TX_USER_MVB_DATA(0)   ,
            TX_MVB_VLD      => TX_USER_MVB_VLD(0)    ,
            TX_MVB_SRC_RDY  => TX_USER_MVB_SRC_RDY(0),
            TX_MVB_DST_RDY  => TX_USER_MVB_DST_RDY(0)
        );
    else generate
        TX_USER_MFB_DATA    <= merg_mfb_data;
        TX_USER_MFB_SOF     <= merg_mfb_sof;
        TX_USER_MFB_EOF     <= merg_mfb_eof;
        TX_USER_MFB_SOF_POS <= merg_mfb_sof_pos;
        TX_USER_MFB_EOF_POS <= merg_mfb_eof_pos;
        TX_USER_MFB_SRC_RDY <= merg_mfb_src_rdy;
        merg_mfb_dst_rdy    <= TX_USER_MFB_DST_RDY;

        TX_USER_MVB_DATA    <= merg_mvb_data;
        TX_USER_MVB_VLD     <= merg_mvb_vld;
        TX_USER_MVB_SRC_RDY <= merg_mvb_src_rdy;
        merg_mvb_dst_rdy    <= TX_USER_MVB_DST_RDY;
    end generate;

end architecture;
