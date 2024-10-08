-- network_mod.vhd: this is the top component of the Network module; 
--                  it contains MI splitter(s) and one or more of the
--                  Network module cores (based on mode of the ethernet
--                  port) which is connected to a pair of MAC lites (RX + TX).
--                  TX input stream is first split per channel, RX channels
--                  are merged into one output stream.
--
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.eth_hdr_pack.all;


architecture FULL of NETWORK_MOD is

    -- =========================================================================
    --                           FUNCTION declarations
    -- =========================================================================
    function region_size_core_f  return natural;

    function region_size_core_f return natural is
    begin
        if (ETH_CORE_ARCH = "F_TILE") then
            case ETH_PORT_SPEED(0) is
                when 400    => return 8;
                when 200    => return 8;
                when 100    => return 4;
                when 50     => return 2;
                when 40     => return 2;
                when 25     => return 1;
                when 10     => return 1;
                when others => return 0;
            end case;
        else
            case ETH_PORT_SPEED(0) is
                when 100    => return 8;
                when 40     => return 4;
                when 25     => return 1;
                when 10     => return 1;
                when others => return 0;
            end case;
        end if;
    end function;

    -- =========================================================================
    --                               CONSTANTS
    -- =========================================================================
    constant EHIP_TYPE         : natural := EHIP_PORT_TYPE(0); -- Define type of used IP core 

    constant REGIONS_CORE      : natural := tsel(ETH_PORT_SPEED(0) = 400, 2, 1); -- TODO: support different speeds/number of channels for each port
    constant REGION_SIZE_CORE  : natural := region_size_core_f;

    constant ETH_CHANNELS      : integer := ETH_PORT_CHAN(0); -- TODO: support different speeds/number of channels for each port
    constant ETH_PORT_STREAMS  : natural := ETH_STREAMS/ETH_PORTS;
    --                                      TSU, Network mod core, ETH_CHANNELS x (TX MAC lite, RX MAC lite)
    constant RESET_REPLICAS    : natural := 1  + 1               + ETH_CHANNELS * (1          + 1          );

    constant PORTS_OFF         : std_logic_vector(MI_ADDR_WIDTH-1 downto 0) := X"0000_2000";
    constant MI_ADDR_BASES     : natural := ETH_PORTS;
    -- MI_PHY for E/F-tile reconfiguration infs
    --                                      NETWORK_MOD_COREs
    constant MI_ADDR_BASES_PHY : natural := ETH_PORTS;
    -- MI Indirect Access offset (X"0000_0020" is enough)
    constant IA_OFF            : std_logic_vector(MI_ADDR_WIDTH_PHY-1 downto 0) := X"0020_0000";

    -- MFB adjustments
    constant MFB_WIDTH      : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant MFB_SOFP_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE));
    constant MFB_EOFP_WIDTH : natural := REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE));

    constant MFB_WIDTH_CORE      : natural := REGIONS_CORE*REGION_SIZE_CORE*BLOCK_SIZE*ITEM_WIDTH;
    constant MFB_SOFP_WIDTH_CORE : natural := REGIONS_CORE*max(1,log2(REGION_SIZE_CORE));
    constant MFB_EOFP_WIDTH_CORE : natural := REGIONS_CORE*max(1,log2(REGION_SIZE_CORE*BLOCK_SIZE));

    constant FPC202_INIT_EN : boolean := (BOARD = "DK-DEV-1SDX-P" or BOARD = "DK-DEV-AGI027RES");
    constant RESIZE_BUFFER  : boolean := (ETH_CORE_ARCH = "F_TILE" or (ETH_CORE_ARCH = "E_TILE" and ETH_CHANNELS = 4));

    constant TS_TIMEOUT_W : natural := 3; -- last TS is unvalided after 4 cycles

    -- =========================================================================
    --                                FUNCTIONS
    -- =========================================================================

    function mi_addr_base_init_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    begin
        for i in 0 to MI_ADDR_BASES-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(PORTS_OFF), MI_ADDR_WIDTH));
        end loop;
        return mi_addr_base_var;
    end function;

    function mi_addr_base_init_phy_f return slv_array_t is
        variable mi_addr_base_var : slv_array_t(MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    begin
        for i in 0 to MI_ADDR_BASES_PHY-1 loop
            mi_addr_base_var(i) := std_logic_vector(resize(i*unsigned(IA_OFF), MI_ADDR_WIDTH_PHY));
        end loop;
        return mi_addr_base_var;
    end function;

    -- =========================================================================
    --                                SIGNALS
    -- =========================================================================
    signal repl_rst_arr : slv_array_t(ETH_PORTS-1 downto 0)(RESET_REPLICAS-1 downto 0);

    -- Interior signals, Network Module Core -> Network Module Logic
    signal rx_mfb_data_i    : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_WIDTH_CORE-1 downto 0);
    signal rx_mfb_sof_pos_i : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_SOFP_WIDTH_CORE-1 downto 0);
    signal rx_mfb_eof_pos_i : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_EOFP_WIDTH_CORE-1 downto 0);
    signal rx_mfb_sof_i     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(REGIONS_CORE-1 downto 0);
    signal rx_mfb_eof_i     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(REGIONS_CORE-1 downto 0);
    signal rx_mfb_error_i   : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(REGIONS_CORE-1 downto 0);
    signal rx_mfb_src_rdy_i : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);

    -- Output of MFB Merger tree (and of the whole Network modul) as an array
    -- MFB signals
    signal tx_usr_mfb_data_arr    : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_WIDTH-1 downto 0);
    signal tx_usr_mfb_sof_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS-1 downto 0);
    signal tx_usr_mfb_eof_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS-1 downto 0);
    signal tx_usr_mfb_sof_pos_arr : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_SOFP_WIDTH-1 downto 0);
    signal tx_usr_mfb_eof_pos_arr : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_EOFP_WIDTH-1 downto 0);
    signal tx_usr_mfb_src_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);
    signal tx_usr_mfb_dst_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);
    -- MVB signals
    signal tx_usr_mvb_data_arr    : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS*ETH_RX_HDR_WIDTH-1 downto 0);
    signal tx_usr_mvb_vld_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS-1 downto 0);
    signal tx_usr_mvb_src_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);
    signal tx_usr_mvb_dst_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);

    -- Deserialized input for TX MAC lite(s)
    signal rx_usr_mfb_data_arr    : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_WIDTH-1 downto 0);
    signal rx_usr_mfb_hdr_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS*ETH_TX_HDR_WIDTH-1 downto 0);
    signal rx_usr_mfb_sof_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS-1 downto 0);
    signal rx_usr_mfb_eof_arr     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(REGIONS-1 downto 0);
    signal rx_usr_mfb_sof_pos_arr : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_SOFP_WIDTH-1 downto 0);
    signal rx_usr_mfb_eof_pos_arr : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0)(MFB_EOFP_WIDTH-1 downto 0);
    signal rx_usr_mfb_src_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);
    signal rx_usr_mfb_dst_rdy_arr : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_PORT_STREAMS-1 downto 0);

    -- Interior signals, Network Module Logic -> Network Module Core
    signal tx_mfb_data_i    : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_WIDTH_CORE-1 downto 0);
    signal tx_mfb_sof_i     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(REGIONS_CORE-1 downto 0);
    signal tx_mfb_eof_i     : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(REGIONS_CORE-1 downto 0);
    signal tx_mfb_sof_pos_i : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_SOFP_WIDTH_CORE-1 downto 0);
    signal tx_mfb_eof_pos_i : slv_array_2d_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0)(MFB_EOFP_WIDTH_CORE-1 downto 0);
    signal tx_mfb_src_rdy_i : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);
    signal tx_mfb_dst_rdy_i : slv_array_t   (ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);

    -- Control/Status signals
    signal sig_activity_rx : slv_array_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);
    signal sig_activity_tx : slv_array_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);
    signal sig_rx_link_up  : slv_array_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);
    signal sig_tx_link_up  : slv_array_t(ETH_PORTS-1 downto 0)(ETH_CHANNELS-1 downto 0);

    -- MI for MAC lites
    signal mi_split_dwr  : slv_array_t     (MI_ADDR_BASES-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_split_addr : slv_array_t     (MI_ADDR_BASES-1 downto 0)(MI_ADDR_WIDTH-1 downto 0);
    signal mi_split_be   : slv_array_t     (MI_ADDR_BASES-1 downto 0)(MI_DATA_WIDTH/8-1 downto 0);
    signal mi_split_rd   : std_logic_vector(MI_ADDR_BASES-1 downto 0);
    signal mi_split_wr   : std_logic_vector(MI_ADDR_BASES-1 downto 0);
    signal mi_split_ardy : std_logic_vector(MI_ADDR_BASES-1 downto 0);
    signal mi_split_drd  : slv_array_t     (MI_ADDR_BASES-1 downto 0)(MI_DATA_WIDTH-1 downto 0);
    signal mi_split_drdy : std_logic_vector(MI_ADDR_BASES-1 downto 0);

    -- MI_PHY for E/F-tile reconfiguration infs
    signal mi_split_dwr_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_split_addr_phy : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_ADDR_WIDTH_PHY-1 downto 0);
    signal mi_split_be_phy   : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY/8-1 downto 0);
    signal mi_split_rd_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_wr_phy   : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_ardy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);
    signal mi_split_drd_phy  : slv_array_t     (MI_ADDR_BASES_PHY-1 downto 0)(MI_DATA_WIDTH_PHY-1 downto 0);
    signal mi_split_drdy_phy : std_logic_vector(MI_ADDR_BASES_PHY-1 downto 0);

    -- TS signals
    signal asfifox_ts_dv_n     : std_logic_vector(ETH_PORTS-1 downto 0);
    signal asfifox_ts_ns       : slv_array_t     (ETH_PORTS-1 downto 0)(64-1 downto 0);
    signal asfifox_ts_timeout  : u_array_t(ETH_PORTS-1 downto 0)(TS_TIMEOUT_W-1 downto 0);
    signal asfifox_ts_last_vld : std_logic_vector(ETH_PORTS-1 downto 0);
    signal synced_ts_dv        : std_logic_vector(ETH_PORTS-1 downto 0);
    signal synced_ts_ns        : slv_array_t     (ETH_PORTS-1 downto 0)(64-1 downto 0);

    -- Demo signals
    signal eth_tx_mvb_channel_arr   : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS*max(1,log2(TX_DMA_CHANNELS))-1 downto 0);
    signal eth_tx_mvb_timestamp_arr : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS*48-1 downto 0);
    signal eth_tx_mvb_vld_arr       : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS-1 downto 0);
    signal demo_asfifo_din          : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS*(max(1,log2(TX_DMA_CHANNELS))+48+1)-1 downto 0);
    signal demo_asfifo_wr           : std_logic_vector(ETH_PORTS-1 downto 0);
    signal demo_asfifo_dout         : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS*(max(1,log2(TX_DMA_CHANNELS))+48+1)-1 downto 0);
    signal demo_asfifo_empty        : std_logic_vector(ETH_PORTS-1 downto 0);
    signal mvb_ch                   : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS_CORE*max(1,log2(TX_DMA_CHANNELS))-1 downto 0);
    signal mvb_ts                   : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS_CORE*48-1 downto 0);
    signal mvb_vld                  : slv_array_t     (ETH_PORTS-1 downto 0)(REGIONS_CORE-1 downto 0);

begin

    -- =========================================================================
    --  Resets replication
    -- =========================================================================
    ports_reset_g : for p in ETH_PORTS-1 downto 0 generate
        network_mod_reset_i : entity work.ASYNC_RESET
        generic map (
            TWO_REG  => false,
            OUT_REG  => true ,
            REPLICAS => RESET_REPLICAS
        )
        port map (
            CLK         => CLK_ETH     (p),
            ASYNC_RST   => RESET_ETH   (p),
            OUT_RST     => repl_rst_arr(p)
        );
    end generate;

    -- =========================================================================
    --  MI SPLITTER for Network Module Logic (MAC Lites)
    -- =========================================================================
    mi_splitter_plus_gen_i : entity work.MI_SPLITTER_PLUS_GEN
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
        -- Common interface ----------
        CLK         => MI_CLK         ,
        RESET       => MI_RESET       ,
        -- Input MI interface --------
        RX_DWR      => MI_DWR         ,
        RX_MWR      => (others => '0'),
        RX_ADDR     => MI_ADDR        ,
        RX_BE       => MI_BE          ,
        RX_RD       => MI_RD          ,
        RX_WR       => MI_WR          ,
        RX_ARDY     => MI_ARDY        ,
        RX_DRD      => MI_DRD         ,
        RX_DRDY     => MI_DRDY        ,
        -- Output MI interfaces ------
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

    -- =========================================================================
    --  MI SPLITTER for reconfiguration of the E/F-Tile(s) and QSFP Control
    -- =========================================================================
    -- QSFP_CTRL is at Port(0), addresses from X"0080_0000" to X"0080_1000",
    -- the rest of the Ports is for Network Module Core(s) with IA_OFF offset.
    mi_splitter_plus_gen_phy_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH  => MI_ADDR_WIDTH_PHY      ,
        DATA_WIDTH  => MI_DATA_WIDTH_PHY      ,
        META_WIDTH  => 0                      ,
        PORTS       => MI_ADDR_BASES_PHY      ,
        PIPE_OUT    => (others => true)       ,
        PIPE_TYPE   => "REG"                  ,
        ADDR_BASES  => MI_ADDR_BASES_PHY      ,
        ADDR_BASE   => mi_addr_base_init_phy_f,
        DEVICE      => DEVICE
    )
    port map(
        -- Common interface -----------
        CLK         => MI_CLK_PHY      ,
        RESET       => MI_RESET_PHY    ,
        -- Input MI interface ---------
        RX_DWR      => MI_DWR_PHY      ,
        RX_MWR      => (others => '0') ,
        RX_ADDR     => MI_ADDR_PHY     ,
        RX_BE       => MI_BE_PHY       ,
        RX_RD       => MI_RD_PHY       ,
        RX_WR       => MI_WR_PHY       ,
        RX_ARDY     => MI_ARDY_PHY     ,
        RX_DRD      => MI_DRD_PHY      ,
        RX_DRDY     => MI_DRDY_PHY     ,
        -- Output MI interfaces -------
        TX_DWR     => mi_split_dwr_phy ,
        TX_ADDR    => mi_split_addr_phy,
        TX_BE      => mi_split_be_phy  ,
        TX_RD      => mi_split_rd_phy  ,
        TX_WR      => mi_split_wr_phy  ,
        TX_ARDY    => mi_split_ardy_phy,
        TX_DRD     => mi_split_drd_phy ,
        TX_DRDY    => mi_split_drdy_phy
    );

    -- =========================================================================
    -- Serialization and deserialization of user MFB+MVB interfaces
    -- =========================================================================

    rx_usr_mfb_data_arr    <= slv_array_2d_deser(RX_MFB_DATA   , ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_hdr_arr     <= slv_array_2d_deser(RX_MFB_HDR    , ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_sof_pos_arr <= slv_array_2d_deser(RX_MFB_SOF_POS, ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_eof_pos_arr <= slv_array_2d_deser(RX_MFB_EOF_POS, ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_sof_arr     <= slv_array_2d_deser(RX_MFB_SOF    , ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_eof_arr     <= slv_array_2d_deser(RX_MFB_EOF    , ETH_PORTS, ETH_PORT_STREAMS);
    rx_usr_mfb_src_rdy_arr <= slv_array_deser(RX_MFB_SRC_RDY, ETH_PORTS);
    RX_MFB_DST_RDY         <= slv_array_ser(rx_usr_mfb_dst_rdy_arr);

    TX_MFB_DATA            <= slv_array_2d_ser(tx_usr_mfb_data_arr);
    TX_MFB_SOF             <= slv_array_2d_ser(tx_usr_mfb_sof_arr);
    TX_MFB_EOF             <= slv_array_2d_ser(tx_usr_mfb_eof_arr);
    TX_MFB_SOF_POS         <= slv_array_2d_ser(tx_usr_mfb_sof_pos_arr);
    TX_MFB_EOF_POS         <= slv_array_2d_ser(tx_usr_mfb_eof_pos_arr);
    TX_MFB_SRC_RDY         <= slv_array_ser(tx_usr_mfb_src_rdy_arr);
    tx_usr_mfb_dst_rdy_arr <= slv_array_deser(TX_MFB_DST_RDY, ETH_PORTS);

    TX_MVB_DATA            <= slv_array_2d_ser(tx_usr_mvb_data_arr);
    TX_MVB_VLD             <= slv_array_2d_ser(tx_usr_mvb_vld_arr);
    TX_MVB_SRC_RDY         <= slv_array_ser(tx_usr_mvb_src_rdy_arr);
    tx_usr_mvb_dst_rdy_arr <= slv_array_deser(TX_MVB_DST_RDY, ETH_PORTS);

    eth_core_g : for p in 0 to ETH_PORTS-1 generate
        -- =====================================================================
        -- Network Module Logic
        -- =====================================================================
        network_mod_logic_i : entity work.NETWORK_MOD_LOGIC
        generic map(
            -- ETH
            ETH_STREAMS      => ETH_PORT_STREAMS,
            ETH_PORT_CHAN    => ETH_PORT_CHAN(p)  ,
            ETH_PORT_ID      => p                 ,
            ETH_PORT_RX_MTU  => ETH_PORT_RX_MTU(p),
            ETH_PORT_TX_MTU  => ETH_PORT_TX_MTU(p),
            ETH_MAC_BYPASS   => ETH_MAC_BYPASS,
            -- MFB
            USER_REGIONS     => REGIONS         ,
            USER_REGION_SIZE => REGION_SIZE     ,
            CORE_REGIONS     => REGIONS_CORE    ,
            CORE_REGION_SIZE => REGION_SIZE_CORE,
            BLOCK_SIZE       => BLOCK_SIZE      ,
            ITEM_WIDTH       => ITEM_WIDTH      ,
            -- MI
            MI_DATA_WIDTH    => MI_DATA_WIDTH   ,
            MI_ADDR_WIDTH    => MI_ADDR_WIDTH   ,
            -- Other
            RESET_USER_WIDTH => RESET_WIDTH     ,
            RESET_CORE_WIDTH => RESET_REPLICAS-2,
            RESIZE_BUFFER    => RESIZE_BUFFER   ,
            DEVICE           => DEVICE          ,
            BOARD            => BOARD
        )
        port map(
            CLK_USER            => CLK_USER,
            CLK_CORE            => CLK_ETH(p),
            RESET_USER          => RESET_USER,
            RESET_CORE          => repl_rst_arr(p)(RESET_REPLICAS-1 downto 2),

            -- Control/status interface
            ACTIVITY_RX         => sig_activity_rx(p),
            ACTIVITY_TX         => sig_activity_tx(p),
            RX_LINK_UP          => sig_rx_link_up (p),
            TX_LINK_UP          => sig_tx_link_up (p),

            -- USER side
            RX_USER_MFB_DATA    => rx_usr_mfb_data_arr   (p),
            RX_USER_MFB_HDR     => rx_usr_mfb_hdr_arr    (p),
            RX_USER_MFB_SOF_POS => rx_usr_mfb_sof_pos_arr(p),
            RX_USER_MFB_EOF_POS => rx_usr_mfb_eof_pos_arr(p),
            RX_USER_MFB_SOF     => rx_usr_mfb_sof_arr    (p),
            RX_USER_MFB_EOF     => rx_usr_mfb_eof_arr    (p),
            RX_USER_MFB_SRC_RDY => rx_usr_mfb_src_rdy_arr(p),
            RX_USER_MFB_DST_RDY => rx_usr_mfb_dst_rdy_arr(p),

            TX_USER_MFB_DATA    => tx_usr_mfb_data_arr   (p),
            TX_USER_MFB_SOF_POS => tx_usr_mfb_sof_pos_arr(p),
            TX_USER_MFB_EOF_POS => tx_usr_mfb_eof_pos_arr(p),
            TX_USER_MFB_SOF     => tx_usr_mfb_sof_arr    (p),
            TX_USER_MFB_EOF     => tx_usr_mfb_eof_arr    (p),
            TX_USER_MFB_SRC_RDY => tx_usr_mfb_src_rdy_arr(p),
            TX_USER_MFB_DST_RDY => tx_usr_mfb_dst_rdy_arr(p),
            TX_USER_MVB_DATA    => tx_usr_mvb_data_arr   (p),
            TX_USER_MVB_VLD     => tx_usr_mvb_vld_arr    (p),
            TX_USER_MVB_SRC_RDY => tx_usr_mvb_src_rdy_arr(p),
            TX_USER_MVB_DST_RDY => tx_usr_mvb_dst_rdy_arr(p),

            -- CORE side
            RX_CORE_MFB_DATA    => rx_mfb_data_i   (p),
            RX_CORE_MFB_SOF_POS => rx_mfb_sof_pos_i(p),
            RX_CORE_MFB_EOF_POS => rx_mfb_eof_pos_i(p),
            RX_CORE_MFB_SOF     => rx_mfb_sof_i    (p),
            RX_CORE_MFB_EOF     => rx_mfb_eof_i    (p),
            RX_CORE_MFB_ERROR   => rx_mfb_error_i  (p),
            RX_CORE_MFB_SRC_RDY => rx_mfb_src_rdy_i(p),

            TX_CORE_MFB_DATA    => tx_mfb_data_i   (p),
            TX_CORE_MFB_SOF_POS => tx_mfb_sof_pos_i(p),
            TX_CORE_MFB_EOF_POS => tx_mfb_eof_pos_i(p),
            TX_CORE_MFB_SOF     => tx_mfb_sof_i    (p),
            TX_CORE_MFB_EOF     => tx_mfb_eof_i    (p),
            TX_CORE_MFB_SRC_RDY => tx_mfb_src_rdy_i(p),
            TX_CORE_MFB_DST_RDY => tx_mfb_dst_rdy_i(p),

            -- MI
            MI_CLK          => MI_CLK          ,
            MI_RESET        => MI_RESET        ,
            MI_DWR          => mi_split_dwr (p),
            MI_ADDR         => mi_split_addr(p),
            MI_RD           => mi_split_rd  (p),
            MI_WR           => mi_split_wr  (p),
            MI_BE           => mi_split_be  (p),
            MI_DRD          => mi_split_drd (p),
            MI_ARDY         => mi_split_ardy(p),
            MI_DRDY         => mi_split_drdy(p),

            TSU_TS_NS       => synced_ts_ns(p),
            TSU_TS_DV       => synced_ts_dv(p)
        );

        -- =====================================================================
        -- Network Module Core
        -- =====================================================================    
        network_mod_core_i: entity work.NETWORK_MOD_CORE 
        generic map (
            ETH_PORT_SPEED    => ETH_PORT_SPEED(p),
            ETH_PORT_CHAN     => ETH_PORT_CHAN (p),
            EHIP_TYPE         => EHIP_TYPE        ,
            LANES             => LANES            ,
            REGIONS           => REGIONS_CORE     ,
            REGION_SIZE       => REGION_SIZE_CORE ,
            BLOCK_SIZE        => BLOCK_SIZE       ,
            ITEM_WIDTH        => ITEM_WIDTH       ,
            MI_DATA_WIDTH_PHY => MI_DATA_WIDTH_PHY,
            MI_ADDR_WIDTH_PHY => MI_ADDR_WIDTH_PHY,
            TS_DEMO_EN        => TS_DEMO_EN       ,
            TX_DMA_CHANNELS   => TX_DMA_CHANNELS  ,
            LANE_RX_POLARITY  => LANE_RX_POLARITY(p*LANES+LANES-1 downto p*LANES),
            LANE_TX_POLARITY  => LANE_TX_POLARITY(p*LANES+LANES-1 downto p*LANES),
            DEVICE            => DEVICE
        )
        port map (
            -- clock and reset
            CLK_ETH         => CLK_ETH(p),
            RESET_ETH       => repl_rst_arr(p)(0),
            -- ETH serial interface
            QSFP_REFCLK_P   => ETH_REFCLK_P(p),
            QSFP_REFCLK_N   => ETH_REFCLK_N(p),
            QSFP_RX_P       => ETH_RX_P(p*LANES+LANES-1 downto p*LANES),
            QSFP_RX_N       => ETH_RX_N(p*LANES+LANES-1 downto p*LANES),
            QSFP_TX_P       => ETH_TX_P(p*LANES+LANES-1 downto p*LANES),
            QSFP_TX_N       => ETH_TX_N(p*LANES+LANES-1 downto p*LANES),
            -- RX interface (packets for transmit to Ethernet, recieved from TX MAC lite)
            RX_MFB_DATA     => tx_mfb_data_i   (p),
            RX_MFB_SOF_POS  => tx_mfb_sof_pos_i(p),
            RX_MFB_EOF_POS  => tx_mfb_eof_pos_i(p),
            RX_MFB_SOF      => tx_mfb_sof_i    (p),
            RX_MFB_EOF      => tx_mfb_eof_i    (p),
            RX_MFB_SRC_RDY  => tx_mfb_src_rdy_i(p),
            RX_MFB_DST_RDY  => tx_mfb_dst_rdy_i(p),

            RX_MVB_CHANNEL   => mvb_ch (p),
            RX_MVB_TIMESTAMP => mvb_ts (p),
            RX_MVB_VLD       => mvb_vld(p),

            TSU_TS_NS       => synced_ts_ns(p),
            TSU_TS_DV       => synced_ts_dv(p),

            -- TX interface (packets received from Ethernet, transmit to RX MAC lite)
            TX_MFB_DATA     => rx_mfb_data_i   (p),
            TX_MFB_SOF_POS  => rx_mfb_sof_pos_i(p),
            TX_MFB_EOF_POS  => rx_mfb_eof_pos_i(p),
            TX_MFB_SOF      => rx_mfb_sof_i    (p),
            TX_MFB_EOF      => rx_mfb_eof_i    (p),
            TX_MFB_ERROR    => rx_mfb_error_i  (p),
            TX_MFB_SRC_RDY  => rx_mfb_src_rdy_i(p),

            -- Control/status
            -- REPEATER_CTRL         => REPEATER_CTRL(p*2+1 downto p*2),
            -- PORT_ENABLED          => PORT_ENABLED(p),
            RX_LINK_UP      => sig_rx_link_up(p),
            TX_LINK_UP      => sig_tx_link_up(p),

            -- MI interface
            MI_CLK_PHY      => MI_CLK,
            MI_RESET_PHY    => MI_RESET,
            MI_DWR_PHY      => mi_split_dwr_phy (p),
            MI_ADDR_PHY     => mi_split_addr_phy(p),
            MI_BE_PHY       => mi_split_be_phy  (p),
            MI_RD_PHY       => mi_split_rd_phy  (p),
            MI_WR_PHY       => mi_split_wr_phy  (p),
            MI_DRD_PHY      => mi_split_drd_phy (p),
            MI_ARDY_PHY     => mi_split_ardy_phy(p),
            MI_DRDY_PHY     => mi_split_drdy_phy(p)
        );

        -- =====================================================================
        -- TIMESTAMP ASFIFOX
        -- =====================================================================
        ts_asfifox_i : entity work.ASFIFOX
        generic map(
            DATA_WIDTH => 64    ,
            ITEMS      => 32    ,
            RAM_TYPE   => "LUT" ,
            FWFT_MODE  => true  ,
            OUTPUT_REG => true  ,
            DEVICE     => DEVICE
        )
        port map (
            WR_CLK    => CLK_ETH     (0)   ,
            WR_RST    => repl_rst_arr(0)(1),
            WR_DATA   => TSU_TS_NS         ,
            WR_EN     => TSU_TS_DV         ,
            WR_FULL   => open              ,
            WR_AFULL  => open              ,
            WR_STATUS => open              ,

            RD_CLK    => CLK_ETH        (p)   ,
            RD_RST    => repl_rst_arr   (p)(1),
            RD_DATA   => asfifox_ts_ns  (p)   ,
            RD_EN     => '1'                  ,
            RD_EMPTY  => asfifox_ts_dv_n(p)   ,
            RD_AEMPTY => open                 ,
            RD_STATUS => open
        );

        process(CLK_ETH)
        begin
            if (rising_edge(CLK_ETH(p))) then
                if (asfifox_ts_dv_n(p) = '1' and asfifox_ts_timeout(p)(TS_TIMEOUT_W-1) = '0') then
                    asfifox_ts_timeout(p) <= asfifox_ts_timeout(p) + 1;
                end if;
                if (repl_rst_arr(p)(1) = '1' or asfifox_ts_dv_n(p) = '0') then
                    asfifox_ts_timeout(p) <= (others => '0');
                end if;
            end if;
        end process;

        process(CLK_ETH)
        begin
            if (rising_edge(CLK_ETH(p))) then
                if (asfifox_ts_dv_n(p) = '0') then
                    asfifox_ts_last_vld(p) <= '1';
                end if;
                if (repl_rst_arr(p)(1) = '1') then
                    asfifox_ts_last_vld(p) <= '0';
                end if;
            end if;
        end process;

        -- Synced TS is valid if the value is current or if the value is a few
        -- clock cycles old. This provides filtering for occasional flushing of
        -- the asynchronous FIFO.
        process(CLK_ETH)
        begin
            if (rising_edge(CLK_ETH(p))) then
                if (asfifox_ts_dv_n(p) = '0') then
                    synced_ts_ns(p) <= asfifox_ts_ns(p);
                end if;
                
                synced_ts_dv(p) <= (not asfifox_ts_dv_n(p)) or
                                   (asfifox_ts_last_vld(p) and not asfifox_ts_timeout(p)(TS_TIMEOUT_W-1));

                if (repl_rst_arr(p)(1) = '1') then
                    synced_ts_dv(p) <= '0';
                end if;
            end if;
        end process;

        -- ETH clock is used as TSU main clock
        TSU_CLK <= CLK_ETH     (0)   ;
        TSU_RST <= repl_rst_arr(0)(1);

        -- =====================================================================
        -- DEMO ASFIFOX for DMA Channels
        -- =====================================================================
        -- WARNING: This logic only supports E-Tile where REGIONS == REGIONS_CORE.

        ts_demo_en_g : if TS_DEMO_EN generate
            eth_tx_mvb_channel_arr   <= slv_array_deser(ETH_TX_MVB_CHANNEL, ETH_PORTS);
            eth_tx_mvb_timestamp_arr <= slv_array_deser(ETH_TX_MVB_TIMESTAMP, ETH_PORTS);
            eth_tx_mvb_vld_arr       <= slv_array_deser(ETH_TX_MVB_VLD, ETH_PORTS);

            -- Sloppy serialization (and deserialization) - do not use elsewhere
            demo_asfifo_din(p) <= eth_tx_mvb_channel_arr(p) & eth_tx_mvb_timestamp_arr(p) & eth_tx_mvb_vld_arr(p);
            demo_asfifo_wr(p) <= or eth_tx_mvb_vld_arr(p);

            demo_asfifox_i : entity work.ASFIFOX
            generic map(
                DATA_WIDTH => REGIONS*(max(1,log2(TX_DMA_CHANNELS))+48+1),
                ITEMS      => 8     ,
                RAM_TYPE   => "LUT" ,
                FWFT_MODE  => true  ,
                OUTPUT_REG => true  ,
                DEVICE     => DEVICE
            )
            port map (
                WR_CLK    => CLK_USER               ,
                WR_RST    => RESET_USER       (0)   ,
                WR_DATA   => demo_asfifo_din  (p)   ,
                WR_EN     => demo_asfifo_wr   (p)   ,
                WR_FULL   => open                   ,
                WR_AFULL  => open                   ,
                WR_STATUS => open                   ,

                RD_CLK    => CLK_ETH          (p)   ,
                RD_RST    => repl_rst_arr     (p)(1),
                RD_DATA   => demo_asfifo_dout (p)   ,
                RD_EN     => '1'                    ,
                RD_EMPTY  => demo_asfifo_empty(p)   ,
                RD_AEMPTY => open                   ,
                RD_STATUS => open
            );

            mvb_ch (p) <= demo_asfifo_dout(p)(REGIONS*(max(1,log2(TX_DMA_CHANNELS))+48+1)-1 downto REGIONS*(48+1));
            mvb_ts (p) <= demo_asfifo_dout(p)(REGIONS*(48+1)-1 downto REGIONS);
            mvb_vld(p) <= demo_asfifo_dout(p)(REGIONS-1 downto 0) and not demo_asfifo_empty(p);
            -- TODO add conversion from REGIONS to REGIONS_CORE...
        else generate
            mvb_ch (p) <= (others => '0');
            mvb_ts (p) <= (others => '0');
            mvb_vld(p) <= (others => '0');
        end generate;
    end generate;

    ACTIVITY_RX <= slv_array_ser(sig_activity_rx);
    ACTIVITY_TX <= slv_array_ser(sig_activity_tx);
    RX_LINK_UP  <= slv_array_ser(sig_rx_link_up);
    TX_LINK_UP  <= slv_array_ser(sig_tx_link_up);

    -- =====================================================================
    -- QSFP control
    -- =====================================================================

    qsfp_ctrl_i : entity work.QSFP_CTRL
    generic map (
       QSFP_PORTS     => QSFP_PORTS,
       QSFP_I2C_PORTS => QSFP_I2C_PORTS,
       FPC202_INIT_EN => FPC202_INIT_EN,
       I2C_TRISTATE   => QSFP_I2C_TRISTATE
    )
    port map (
       RST            => MI_RESET_PMD,
       --
       TX_READY       => (others => '1'),
       -- QSFP control/status
       QSFP_MODSEL_N  => QSFP_MODSEL_N,
       QSFP_LPMODE    => QSFP_LPMODE,
       QSFP_RESET_N   => QSFP_RESET_N,
       QSFP_MODPRS_N  => QSFP_MODPRS_N,
       QSFP_INT_N     => QSFP_INT_N,
       QSFP_I2C_SCL   => QSFP_I2C_SCL,
       QSFP_I2C_SDA   => QSFP_I2C_SDA,
       QSFP_I2C_DIR   => QSFP_I2C_DIR,
       QSFP_I2C_SDA_I => QSFP_I2C_SDA_I,
       QSFP_I2C_SCL_I => QSFP_I2C_SCL_I,
       QSFP_I2C_SCL_O  => QSFP_I2C_SCL_O,
       QSFP_I2C_SCL_OE => QSFP_I2C_SCL_OE,
       QSFP_I2C_SDA_O  => QSFP_I2C_SDA_O,
       QSFP_I2C_SDA_OE => QSFP_I2C_SDA_OE,
       -- Select which QSFP port is targetting during MI read/writes
       MI_QSFP_SEL    => MI_ADDR_PMD(8+max(log2(QSFP_PORTS),1)-1 downto 8),
       -- MI interface
       MI_CLK_PHY     => MI_CLK_PMD  ,
       MI_RESET_PHY   => MI_RESET_PMD,
       MI_DWR_PHY     => MI_DWR_PMD  ,
       MI_ADDR_PHY    => MI_ADDR_PMD ,
       MI_RD_PHY      => MI_RD_PMD   ,
       MI_WR_PHY      => MI_WR_PMD   ,
       MI_BE_PHY      => MI_BE_PMD   ,
       MI_DRD_PHY     => MI_DRD_PMD  ,
       MI_ARDY_PHY    => MI_ARDY_PMD ,
       MI_DRDY_PHY    => MI_DRDY_PMD
    );

end architecture;
