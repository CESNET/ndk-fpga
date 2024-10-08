-- tx_mac_lite.vhd: TX MAC Lite top level module
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE is
    generic(
        -- =====================================================================
        -- MFB CONFIGURATION:
        -- =====================================================================
        -- TX MFB configuration, allows you to set the required output data width
        -- according to the selected Ethernet standard.
        -- ---------------------------------------------------------------------

        -- TX MFB: number of regions in word, must be power of 2
        TX_REGIONS     : natural := 4;
        -- TX MFB: number of blocks in region, must be power of 2
        TX_REGION_SIZE : natural := 8;
        -- TX MFB: number of items in block, must be 8 or 4
        TX_BLOCK_SIZE  : natural := 8;
        -- TX MFB: width of one item in bits, must be 8
        TX_ITEM_WIDTH  : natural := 8;

        -- RX MFB configuration, by default the same as TX. Useful, for example,
        -- for narrowing data width from 512b (RX) to 128b (TX).
        -- ---------------------------------------------------------------------

        -- RX MFB: number of regions in word, by default same as TX
        RX_REGIONS     : natural := TX_REGIONS;
        -- RX MFB: number of blocks in region, by default same as TX
        RX_REGION_SIZE : natural := TX_REGION_SIZE;
        -- RX MFB: number of items in block, by default same as TX
        RX_BLOCK_SIZE  : natural := TX_BLOCK_SIZE;
        -- RX MFB: width of one item in bits, by default same as TX
        RX_ITEM_WIDTH  : natural := TX_ITEM_WIDTH;

        -- This generic determines the position of the logic that converts the
        -- MFB bus from RX to TX parameters. By default (False) the conversion
        -- is performed immediately on the TX_MAC_LITE input, otherwise (True)
        -- it is performed on the output. RESIZE_ON_TX=True cannot be combined
        -- with IPG_GENERATE_EN=True.
        RESIZE_ON_TX   : boolean := False;

        -- =====================================================================
        -- OTHERS CONFIGURATION:
        -- =====================================================================

        -- Maximum allowed size of packet in bytes.
        PKT_MTU_BYTES   : natural := 16384;
        -- Set true when CRC checksum is included in frames on RX MFB stream.
        RX_INCLUDE_CRC  : boolean := False;
        -- Set true when free items for CRC checksum (when RX_INCLUDE_CRC=false)
        -- and Inter Packet Gaps (IPG) are included on RX MFB stream.
        RX_INCLUDE_IPG  : boolean := True;
        -- Set true when you need generate and insert CRC to frames.
        CRC_INSERT_EN   : boolean := True;
        -- Set true when you need generate Inter Packet Gaps (IPG).
        IPG_GENERATE_EN : boolean := False;
        -- Set true when you need use counters implemented in DSP.
        USE_DSP_CNT     : boolean := False;
        -- Maximum number of Transactions waiting for space insertion
        -- Ignored when IPG_GENERATE_EN==false
        TRANS_FIFO_SIZE : natural := 128;
        -- FPGA device name.
        DEVICE          : string := "STRATIX10";
        -- Targeted version of Ethernet standart
        -- Ignored when IPG_GENERATE_EN==false
        -- Defines minimum size of inter-packet gap according to Deficit Idle Count
        -- Possible values: "10Gb", "over10Gb"
        ETH_VERSION     : string := "over10Gb"
    );
    port(
        -- =====================================================================
        --  MI32 INTERFACE (MI_CLK)
        -- =====================================================================

        -- Clock for MI bus
        MI_CLK         : in  std_logic;
        -- Reset synchronized with MI_CLK
        MI_RESET       : in  std_logic;
        -- MI bus: data from master to slave (write data)
        MI_DWR         : in  std_logic_vector(31 downto 0);
        -- MI bus: slave address
        MI_ADDR        : in  std_logic_vector(31 downto 0);
        -- MI bus: byte enable
        MI_RD          : in  std_logic;
        -- MI bus: read request
        MI_WR          : in  std_logic;
        -- MI bus: write request
        MI_BE          : in  std_logic_vector(3 downto 0);
        -- MI bus: ready of slave module
        MI_DRD         : out std_logic_vector(31 downto 0);
        -- MI bus: data from slave to master (read data)
        MI_ARDY        : out std_logic;
        -- MI bus: valid of MI_DRD data signal
        MI_DRDY        : out std_logic;

        -- =====================================================================
        --  RX MFB INPUT STREAM
        -- =====================================================================

        -- Clock for RX MFB interface
        RX_CLK         : in  std_logic;
        -- Clock for RX MFB interface with double frequency (only for CrossbarX)
        RX_CLK_X2      : in  std_logic;
        -- Reset synchronized with RX_CLK
        RX_RESET       : in  std_logic;
        -- RX MFB: data word with frames (packets)
        RX_MFB_DATA    : in  std_logic_vector(RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        -- RX MFB: Start Of Frame (SOF) flag for each MFB region
        RX_MFB_SOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);
        -- RX MFB: End Of Frame (EOF) flag for each MFB region
        RX_MFB_EOF_POS : in  std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        -- RX MFB: SOF position for each MFB region in MFB blocks
        RX_MFB_SOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        -- RX MFB: EOF position for each MFB region in MFB items
        RX_MFB_EOF     : in  std_logic_vector(RX_REGIONS-1 downto 0);
        -- RX MFB: source ready of each MFB bus
        RX_MFB_SRC_RDY : in  std_logic;
        -- RX MFB: destination ready of each MFB bus
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        --  TX MFB OUTPUT STREAM
        -- =====================================================================
        --  Without gaps inside packet, include CRC and IPG (optional).

        -- Clock for TX MFB interface
        TX_CLK         : in  std_logic;
        -- Reset synchronized with TX_CLK
        TX_RESET       : in  std_logic;
        -- TX MFB: data word with frames (packets) include CRC and IPG (optional).
        TX_MFB_DATA    : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
        -- TX MFB: Start Of Frame (SOF) flag for each MFB region
        TX_MFB_SOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE))-1 downto 0);
        -- TX MFB: End Of Frame (EOF) flag for each MFB region
        TX_MFB_EOF_POS : out std_logic_vector(TX_REGIONS*max(1,log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
        -- TX MFB: SOF position for each MFB region in MFB blocks
        TX_MFB_SOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
        -- TX MFB: EOF position for each MFB region in MFB items
        TX_MFB_EOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
        -- TX MFB: source ready of each MFB bus, without gaps inside packet
        TX_MFB_SRC_RDY : out std_logic;
        -- TX MFB: destination ready of each MFB bus
        TX_MFB_DST_RDY : in  std_logic;

        -- =====================================================================
        -- OUTPUT LINK STATUS INTERFACE (TX_CLK)
        -- =====================================================================

        -- Links status (TX_CLK): Active during frame transmission
        OUTGOING_FRAME : out std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE is

    function fce_crcfifo_afull_threshold(
        REGION_SIZE  : natural;
        BLOCK_SIZE   : natural;
        CRC_END_IMPL : string
    )
    return natural is
    begin
        if (REGION_SIZE = 1 and BLOCK_SIZE = 1) then
            return 7;
        elsif (CRC_END_IMPL = "SHIFTER") then
            return 8;
        else
            return 6+log2(REGION_SIZE*BLOCK_SIZE);
        end if;
    end;

    constant MD_REGIONS          : natural := tsel(RESIZE_ON_TX,RX_REGIONS,TX_REGIONS);
    constant MD_REGION_SIZE      : natural := tsel(RESIZE_ON_TX,RX_REGION_SIZE,TX_REGION_SIZE);
    constant MD_BLOCK_SIZE       : natural := tsel(RESIZE_ON_TX,RX_BLOCK_SIZE,TX_BLOCK_SIZE);
    constant MD_ITEM_WIDTH       : natural := tsel(RESIZE_ON_TX,RX_ITEM_WIDTH,TX_ITEM_WIDTH);

    constant MD_DATA_W           : natural := MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH;

    constant NUM_OF_PKTS         : natural := tsel(DEVICE="ULTRASCALE" and TX_REGIONS = 1 and TX_REGION_SIZE = 1,1,4);
    constant LEN_WIDTH           : natural := log2(PKT_MTU_BYTES+1);
    constant DFIFO_ITEMS         : natural := 2**log2(div_roundup((PKT_MTU_BYTES+1),(MD_DATA_W/8)));
    constant FRAME_LEN_MIN       : natural := tsel(RX_INCLUDE_CRC,64,60);
    constant CRC_GEN             : boolean := CRC_INSERT_EN and not RX_INCLUDE_CRC;
    constant SPACER_GEN          : boolean := (CRC_GEN and not RX_INCLUDE_IPG) or IPG_GENERATE_EN;
    constant CRC_WIDTH           : natural := 4*MD_ITEM_WIDTH;
    constant CRC_END_IMPL        : string  := "TREE";
    constant CRC_ASFIFO_ITEMS    : natural := 512; -- Must approximately match the latency Spacer otherwise reduces throughput.
    constant CRC_ASFIFO_RAM_TYPE : string  := "AUTO";
    constant CRC_ASFIFO_AFULL_TH : natural := fce_crcfifo_afull_threshold(MD_REGION_SIZE,MD_BLOCK_SIZE,CRC_END_IMPL);

    signal rx_mfb_sof_pos_fix          : std_logic_vector(RX_REGIONS*max(1,log2(RX_REGION_SIZE))-1 downto 0);

    signal rc_mfb_data                 : std_logic_vector(MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH-1 downto 0);
    signal rc_mfb_sof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE))-1 downto 0);
    signal rc_mfb_eof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE*MD_BLOCK_SIZE))-1 downto 0);
    signal rc_mfb_sof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal rc_mfb_eof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal rc_mfb_src_rdy              : std_logic;
    signal rc_mfb_dst_rdy              : std_logic;

    signal rc_mfb_src_rdy_len          : std_logic;
    signal rc_mfb_dst_rdy_len          : std_logic;

    signal fl_mfb_data                 : std_logic_vector(MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH-1 downto 0);
    signal fl_mfb_sof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE))-1 downto 0);
    signal fl_mfb_eof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE*MD_BLOCK_SIZE))-1 downto 0);
    signal fl_mfb_sof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal fl_mfb_eof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal fl_mfb_src_rdy              : std_logic;
    signal fl_mfb_dst_rdy              : std_logic;

    signal fl_mfb_frame_len            : std_logic_vector(MD_REGIONS*LEN_WIDTH-1 downto 0);
    signal fl_mfb_frame_len_arr        : slv_array_t(MD_REGIONS-1 downto 0)(LEN_WIDTH-1 downto 0);
    signal fl_mfb_undersize            : std_logic_vector(MD_REGIONS-1 downto 0);
    signal fl_mfb_discard              : std_logic_vector(MD_REGIONS-1 downto 0);

    signal crc_mfb_src_rdy             : std_logic;
    signal crc_mfb_dst_rdy             : std_logic;

    signal crc32_data                  : std_logic_vector(MD_REGIONS*CRC_WIDTH-1 downto 0);
    signal crc32_vld                   : std_logic_vector(MD_REGIONS-1 downto 0);
    signal crc32_src_rdy               : std_logic;

    signal cd_fifo_di                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal cd_fifo_wr                  : std_logic;
    signal cd_fifo_full                : std_logic;
    signal cd_fifo_do                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal cd_fifo_rd                  : std_logic;
    signal cd_fifo_empty               : std_logic;

    signal cd_fifo_overflow_dbg_reg    : std_logic;
    signal cd_fifo_underflow_dbg_reg   : std_logic;

    signal crc32_vld_masked            : std_logic_vector(MD_REGIONS-1 downto 0);
    signal crc32_src_rdy_masked        : std_logic;

    signal af_crc32_afull              : std_logic;
    signal af_crc32_afull_reg          : std_logic;
    signal af_crc32_data               : std_logic_vector(MD_REGIONS*CRC_WIDTH-1 downto 0);
    signal af_crc32_vld                : std_logic_vector(MD_REGIONS-1 downto 0);
    signal af_crc32_src_rdy            : std_logic;
    signal af_crc32_dst_rdy            : std_logic;

    signal fd_mfb_data                 : std_logic_vector(MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH-1 downto 0);
    signal fd_mfb_sof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE))-1 downto 0);
    signal fd_mfb_eof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE*MD_BLOCK_SIZE))-1 downto 0);
    signal fd_mfb_sof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal fd_mfb_eof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal fd_mfb_src_rdy              : std_logic;
    signal fd_mfb_dst_rdy              : std_logic;

    signal fd_mfb_frame_len            : std_logic_vector(MD_REGIONS*LEN_WIDTH-1 downto 0);
    signal fd_mfb_discard              : std_logic_vector(MD_REGIONS-1 downto 0);

    signal sp_mfb_data                 : std_logic_vector(MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH-1 downto 0);
    signal sp_mfb_sof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE))-1 downto 0);
    signal sp_mfb_eof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE*MD_BLOCK_SIZE))-1 downto 0);
    signal sp_mfb_sof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal sp_mfb_eof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal sp_mfb_src_rdy              : std_logic;
    signal sp_mfb_dst_rdy              : std_logic;

    signal cg_mfb_data                 : std_logic_vector(MD_REGIONS*MD_REGION_SIZE*MD_BLOCK_SIZE*MD_ITEM_WIDTH-1 downto 0);
    signal cg_mfb_sof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE))-1 downto 0);
    signal cg_mfb_eof_pos              : std_logic_vector(MD_REGIONS*max(1,log2(MD_REGION_SIZE*MD_BLOCK_SIZE))-1 downto 0);
    signal cg_mfb_sof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal cg_mfb_eof                  : std_logic_vector(MD_REGIONS-1 downto 0);
    signal cg_mfb_src_rdy              : std_logic;
    signal cg_mfb_dst_rdy              : std_logic;

    signal tx_inc_frame                : std_logic_vector(TX_REGIONS+1-1 downto 0);
    signal tx_gap_inside_frame_dbg     : std_logic;
    signal tx_gap_inside_frame_dbg_reg : std_logic;

    signal stat_rx_frame_inc_reg       : std_logic_vector(MD_REGIONS-1 downto 0);
    signal stat_tx_frame_inc_reg       : std_logic_vector(MD_REGIONS-1 downto 0);
    signal stat_tx_frame_length_reg    : std_logic_vector(MD_REGIONS*LEN_WIDTH-1 downto 0);
    signal stat_discard_frame_inc_reg  : std_logic_vector(MD_REGIONS-1 downto 0);

    signal stat_total_frames           : std_logic_vector(64-1 downto 0);
    signal stat_total_sent_frames      : std_logic_vector(64-1 downto 0);
    signal stat_total_sent_octects     : std_logic_vector(64-1 downto 0);
    signal stat_total_discarded_frames : std_logic_vector(64-1 downto 0);

    signal ctrl_strobe_cnt             : std_logic;
    signal ctrl_reset_cnt              : std_logic;
    signal ctrl_obuf_en                : std_logic;

begin

    -- =========================================================================
    --  MFB RECONFIGURATOR
    -- =========================================================================

    rx_mfb_sof_pos_fix_g : if RX_REGION_SIZE > 1 generate
        rx_mfb_sof_pos_fix <= RX_MFB_SOF_POS;
    else generate
        rx_mfb_sof_pos_fix <= (others => '0');
    end generate;

    mfb_reconf_i : entity work.MFB_RECONFIGURATOR
    generic map(
        RX_REGIONS           => RX_REGIONS,
        RX_REGION_SIZE       => RX_REGION_SIZE,
        RX_BLOCK_SIZE        => RX_BLOCK_SIZE,
        RX_ITEM_WIDTH        => RX_ITEM_WIDTH,
        TX_REGIONS           => MD_REGIONS,
        TX_REGION_SIZE       => MD_REGION_SIZE,
        TX_BLOCK_SIZE        => MD_BLOCK_SIZE,
        TX_ITEM_WIDTH        => MD_ITEM_WIDTH,
        FIFO_SIZE            => 32,
        FRAMES_OVER_TX_BLOCK => 0,
        DEVICE               => DEVICE
    )
    port map(
        CLK        => RX_CLK,
        RESET      => RX_RESET,

        RX_DATA    => RX_MFB_DATA,
        RX_SOF     => RX_MFB_SOF,
        RX_EOF     => RX_MFB_EOF,
        RX_SOF_POS => rx_mfb_sof_pos_fix,
        RX_EOF_POS => RX_MFB_EOF_POS,
        RX_SRC_RDY => RX_MFB_SRC_RDY,
        RX_DST_RDY => RX_MFB_DST_RDY,

        TX_DATA    => rc_mfb_data,
        TX_SOF     => rc_mfb_sof,
        TX_EOF     => rc_mfb_eof,
        TX_SOF_POS => rc_mfb_sof_pos,
        TX_EOF_POS => rc_mfb_eof_pos,
        TX_SRC_RDY => rc_mfb_src_rdy,
        TX_DST_RDY => rc_mfb_dst_rdy
    );

    -- =========================================================================
    --  FRAME LENGTH CALCULATOR AND DISCARD FLAG GENERATOR
    -- =========================================================================

    rc_mfb_src_rdy_len <= rc_mfb_src_rdy and ctrl_obuf_en;
    rc_mfb_dst_rdy     <= rc_mfb_dst_rdy_len and ctrl_obuf_en;

    mfb_frame_len_i : entity work.MFB_FRAME_LNG
    generic map(
        REGIONS        => MD_REGIONS,
        REGION_SIZE    => MD_REGION_SIZE,
        BLOCK_SIZE     => MD_BLOCK_SIZE,
        ITEM_WIDTH     => MD_ITEM_WIDTH,
        META_WIDTH     => 1,
        LNG_WIDTH      => LEN_WIDTH,
        REG_BITMAP     => "111",
        IMPLEMENTATION => "parallel"
    )
    port map(
        CLK          => RX_CLK,
        RESET        => RX_RESET,

        RX_DATA      => rc_mfb_data,
        RX_META      => (others => '0'),
        RX_SOF_POS   => rc_mfb_sof_pos,
        RX_EOF_POS   => rc_mfb_eof_pos,
        RX_SOF       => rc_mfb_sof,
        RX_EOF       => rc_mfb_eof,
        RX_SRC_RDY   => rc_mfb_src_rdy_len,
        RX_DST_RDY   => rc_mfb_dst_rdy_len,

        TX_DATA      => fl_mfb_data,
        TX_META      => open,
        TX_SOF_POS   => fl_mfb_sof_pos,
        TX_EOF_POS   => fl_mfb_eof_pos,
        TX_SOF       => fl_mfb_sof,
        TX_EOF       => fl_mfb_eof,
        TX_COF       => open,
        TX_TEMP_LNG  => open,
        TX_FRAME_LNG => fl_mfb_frame_len,
        TX_SRC_RDY   => fl_mfb_src_rdy,
        TX_DST_RDY   => fl_mfb_dst_rdy
    );

    fl_mfb_frame_len_arr <= slv_array_deser(fl_mfb_frame_len,MD_REGIONS,LEN_WIDTH);

    fl_mfb_discard_g : for r in 0 to MD_REGIONS-1 generate
        fl_mfb_undersize(r) <= '1' when (unsigned(fl_mfb_frame_len_arr(r)) < FRAME_LEN_MIN) else '0';
        fl_mfb_discard(r)   <= fl_mfb_undersize(r) and fl_mfb_eof(r) and fl_mfb_src_rdy;
    end generate;

    fl_mfb_dst_rdy <= fd_mfb_dst_rdy and crc_mfb_dst_rdy;

    process (RX_CLK)
    begin
        if rising_edge(RX_CLK) then
            if (fd_mfb_dst_rdy = '1') then
                fd_mfb_data      <= fl_mfb_data;
                fd_mfb_sof       <= fl_mfb_sof;
                fd_mfb_eof       <= fl_mfb_eof;
                fd_mfb_sof_pos   <= fl_mfb_sof_pos;
                fd_mfb_eof_pos   <= fl_mfb_eof_pos;
                fd_mfb_frame_len <= fl_mfb_frame_len;
                fd_mfb_discard   <= fl_mfb_discard;
            end if;
        end if;
    end process;

    process (RX_CLK)
    begin
        if rising_edge(RX_CLK) then
            if (RX_RESET = '1') then
                fd_mfb_src_rdy <= '0';
            elsif (fd_mfb_dst_rdy = '1') then
                fd_mfb_src_rdy <= fl_mfb_src_rdy and crc_mfb_dst_rdy;
            end if;
        end if;
    end process;

    -- =========================================================================
    --  FRAME CRC32 GENERATOR AND CRC32 ASFIFO
    -- =========================================================================

    crc_mfb_src_rdy <= fl_mfb_src_rdy and fl_mfb_dst_rdy and crc_mfb_dst_rdy;

    crc_gen_g : if CRC_GEN generate
        crc_gen_i : entity work.TX_MAC_LITE_CRC_GEN
        generic map(
            REGIONS        => MD_REGIONS,
            REGION_SIZE    => MD_REGION_SIZE,
            BLOCK_SIZE     => MD_BLOCK_SIZE,
            ITEM_WIDTH     => MD_ITEM_WIDTH,
            CRC_END_IMPL   => CRC_END_IMPL
        )
        port map(
            -- CLOCK AND RESET
            CLK           => RX_CLK,
            RESET         => RX_RESET,
            -- INPUT MFB
            RX_DATA       => fl_mfb_data,
            RX_SOF_POS    => fl_mfb_sof_pos,
            RX_EOF_POS    => fl_mfb_eof_pos,
            RX_SOF        => fl_mfb_sof,
            RX_EOF        => fl_mfb_eof,
            RX_SRC_RDY    => crc_mfb_src_rdy,
            -- OUTPUT
            CRC_DATA      => crc32_data,
            CRC_VLD       => crc32_vld,
            CRC_SRC_RDY   => crc32_src_rdy
        );

        -- ---------------------------------------------------------------------
        -- CRC32 DISCARD FIFO
        -- ---------------------------------------------------------------------

        cd_fifo_wr <= (or fl_mfb_eof) and crc_mfb_src_rdy;
        cd_fifo_di <= fl_mfb_eof and not fl_mfb_undersize;

        process (RX_CLK)
        begin
            if (rising_edge(RX_CLK)) then
                cd_fifo_overflow_dbg_reg <= cd_fifo_wr and cd_fifo_full;
            end if;
        end process;

        assert (cd_fifo_overflow_dbg_reg /= '1')
            report "TX_MAC_LITE: crc_discard_fifo_i overflow!"
            severity failure;

        crc_discard_fifo_i : entity work.FIFOX
        generic map(
            DATA_WIDTH          => MD_REGIONS,
            ITEMS               => 32,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 1,
            ALMOST_EMPTY_OFFSET => 1
        )
        port map(
            CLK    => RX_CLK,
            RESET  => RX_RESET,

            DI     => cd_fifo_di,
            WR     => cd_fifo_wr,
            FULL   => cd_fifo_full, -- debug only
            AFULL  => open,

            DO     => cd_fifo_do,
            RD     => cd_fifo_rd,
            EMPTY  => cd_fifo_empty, -- debug only
            AEMPTY => open
        );

        process (RX_CLK)
        begin
            if (rising_edge(RX_CLK)) then
                cd_fifo_underflow_dbg_reg <= cd_fifo_rd and cd_fifo_empty;
            end if;
        end process;

        assert (cd_fifo_underflow_dbg_reg /= '1')
            report "TX_MAC_LITE: crc_discard_fifo_i underflow!"
            severity failure;

        cd_fifo_rd <= crc32_src_rdy;

        -- ---------------------------------------------------------------------
        -- CRC32 ASFIFO
        -- ---------------------------------------------------------------------

        -- Discard CRC of undersized frames
        crc32_vld_masked <= crc32_vld and cd_fifo_do and crc32_src_rdy;
        crc32_src_rdy_masked <= or crc32_vld_masked;

        crc_asfifo_i : entity work.MVB_ASFIFOX
        generic map(
            MVB_ITEMS          => MD_REGIONS,
            MVB_ITEM_WIDTH     => CRC_WIDTH,
            FIFO_ITEMS         => CRC_ASFIFO_ITEMS,
            RAM_TYPE           => CRC_ASFIFO_RAM_TYPE,
            FWFT_MODE          => True,
            OUTPUT_REG         => False,
            ALMOST_FULL_OFFSET => CRC_ASFIFO_AFULL_TH,
            DEVICE             => DEVICE
        )
        port map(
            RX_CLK     => RX_CLK,
            RX_RESET   => RX_RESET,
            RX_DATA    => crc32_data,
            RX_VLD     => crc32_vld_masked,
            RX_SRC_RDY => crc32_src_rdy_masked,
            RX_DST_RDY => open,
            RX_AFULL   => af_crc32_afull,

            TX_CLK     => TX_CLK,
            TX_RESET   => TX_RESET,
            TX_DATA    => af_crc32_data,
            TX_VLD     => af_crc32_vld,
            TX_SRC_RDY => af_crc32_src_rdy,
            TX_DST_RDY => af_crc32_dst_rdy
        );

        af_crc32_afull_reg_p : process (RX_CLK)
        begin
            if (rising_edge(RX_CLK)) then
                if (RX_RESET = '1') then
                    af_crc32_afull_reg <= '1';
                else
                    af_crc32_afull_reg <= af_crc32_afull;
                end if;
            end if;
        end process;

        crc_mfb_dst_rdy <= not af_crc32_afull_reg;

    else generate
        crc_mfb_dst_rdy <= '1';
    end generate;

    -- =========================================================================
    --  SPACER/BUFFER - buffering, free items for CRC and IPG generation (optional)
    -- =========================================================================

    spacer_g : if SPACER_GEN generate
        spacer_i : entity work.CROSSBARX_STREAM
        generic map(
            CX_USE_CLK2           => false,
            CX_USE_CLK_ARB        => false,
            OBUF_META_EQ_OUTPUT   => false,
            OBUF_INPUT_EQ_OUTPUT  => false,
            MFB_REGIONS           => MD_REGIONS,
            MFB_REGION_SIZE       => MD_REGION_SIZE,
            MFB_BLOCK_SIZE        => MD_BLOCK_SIZE,
            MFB_ITEM_WIDTH        => MD_ITEM_WIDTH,
            PKT_MTU               => PKT_MTU_BYTES,
            NUM_OF_PKTS           => NUM_OF_PKTS,
            TRANS_FIFO_SIZE       => TRANS_FIFO_SIZE,
            F_GAP_ADJUST_EN       => true,
            F_GAP_ADJUST_SIZE_AVG => 24,
            F_GAP_ADJUST_SIZE_MIN => tsel((ETH_VERSION="10Gb"),24-3,24-7),
            F_EXTEND_START_EN     => false,
            F_EXTEND_START_SIZE   => 4,
            F_EXTEND_END_EN       => false,
            F_EXTEND_END_SIZE     => 4,
            DEVICE                => DEVICE
        )
        port map(
            RX_CLK         => RX_CLK,
            RX_CLK2        => RX_CLK_X2,
            RX_RESET       => RX_RESET,
            TX_CLK         => TX_CLK,
            TX_RESET       => TX_RESET,
            CX_CLK_ARB     => RX_CLK,
            CX_RESET_ARB   => RX_RESET,

            RX_MFB_DATA    => fd_mfb_data,
            RX_MFB_DISCARD => fd_mfb_discard,
            RX_MFB_SOF_POS => fd_mfb_sof_pos,
            RX_MFB_EOF_POS => fd_mfb_eof_pos,
            RX_MFB_SOF     => fd_mfb_sof,
            RX_MFB_EOF     => fd_mfb_eof,
            RX_MFB_SRC_RDY => fd_mfb_src_rdy,
            RX_MFB_DST_RDY => fd_mfb_dst_rdy,

            TX_MFB_DATA    => sp_mfb_data,
            TX_MFB_SOF_POS => sp_mfb_sof_pos,
            TX_MFB_EOF_POS => sp_mfb_eof_pos,
            TX_MFB_SOF     => sp_mfb_sof,
            TX_MFB_EOF     => sp_mfb_eof,
            TX_MFB_SRC_RDY => sp_mfb_src_rdy,
            TX_MFB_DST_RDY => sp_mfb_dst_rdy
        );
    else generate
        buffer_i : entity work.MFB_PD_ASFIFO
        generic map(
            ITEMS              => DFIFO_ITEMS,
            -- More time is needed to calculate CRC.
            -- Lack of time is reported as error: "TX_MAC_LITE_CRC_INSERT: CRC32 out of sync!".
            WR_PTR_ADD_LATENCY => 16,
            REGIONS            => MD_REGIONS,
            REGION_SIZE        => MD_REGION_SIZE,
            BLOCK_SIZE         => MD_BLOCK_SIZE,
            ITEM_WIDTH         => MD_ITEM_WIDTH,
            DEVICE             => DEVICE
        )
        port map(
            RX_CLK           => RX_CLK,
            RX_RESET         => RX_RESET,
            RX_DATA          => fd_mfb_data,
            RX_SOF_POS       => fd_mfb_sof_pos,
            RX_EOF_POS       => fd_mfb_eof_pos,
            RX_SOF           => fd_mfb_sof,
            RX_EOF           => fd_mfb_eof,
            RX_SRC_RDY       => fd_mfb_src_rdy,
            RX_DST_RDY       => fd_mfb_dst_rdy,
            RX_DISCARD       => fd_mfb_discard,
            RX_FORCE_DISCARD => '0',
            STATUS           => open,

            TX_CLK           => TX_CLK,
            TX_RESET         => TX_RESET,
            TX_DATA          => sp_mfb_data,
            TX_SOF_POS       => sp_mfb_sof_pos,
            TX_EOF_POS       => sp_mfb_eof_pos,
            TX_SOF           => sp_mfb_sof,
            TX_EOF           => sp_mfb_eof,
            TX_SRC_RDY       => sp_mfb_src_rdy,
            TX_DST_RDY       => sp_mfb_dst_rdy
        );
    end generate;

    -- =========================================================================
    --  CRC INSERT MODULE
    -- =========================================================================

    crc_insert_g : if CRC_GEN generate
        crc_insert_i : entity work.TX_MAC_LITE_CRC_INSERT
        generic map(
            MFB_REGIONS     => MD_REGIONS,
            MFB_REGION_SIZE => MD_REGION_SIZE,
            MFB_BLOCK_SIZE  => MD_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MD_ITEM_WIDTH,
            DEVICE          => DEVICE
        )
        port map(
            CLK                => TX_CLK,
            RESET              => TX_RESET,

            RX_MVB_CRC_DATA    => af_crc32_data,
            RX_MVB_CRC_VLD     => af_crc32_vld,
            RX_MVB_CRC_SRC_RDY => af_crc32_src_rdy,
            RX_MVB_CRC_DST_RDY => af_crc32_dst_rdy,

            RX_MFB_DATA        => sp_mfb_data,
            RX_MFB_SOF         => sp_mfb_sof,
            RX_MFB_EOF         => sp_mfb_eof,
            RX_MFB_SOF_POS     => sp_mfb_sof_pos,
            RX_MFB_EOF_POS     => sp_mfb_eof_pos,
            RX_MFB_SRC_RDY     => sp_mfb_src_rdy,
            RX_MFB_DST_RDY     => sp_mfb_dst_rdy,

            TX_MFB_DATA        => cg_mfb_data,
            TX_MFB_SOF         => cg_mfb_sof,
            TX_MFB_EOF         => cg_mfb_eof,
            TX_MFB_SOF_POS     => cg_mfb_sof_pos,
            TX_MFB_EOF_POS     => cg_mfb_eof_pos,
            TX_MFB_SRC_RDY     => cg_mfb_src_rdy,
            TX_MFB_DST_RDY     => cg_mfb_dst_rdy
        );
    else generate
        cg_mfb_data    <= sp_mfb_data;
        cg_mfb_sof     <= sp_mfb_sof;
        cg_mfb_eof     <= sp_mfb_eof;
        cg_mfb_sof_pos <= sp_mfb_sof_pos;
        cg_mfb_eof_pos <= sp_mfb_eof_pos;
        cg_mfb_src_rdy <= sp_mfb_src_rdy;
        sp_mfb_dst_rdy <= cg_mfb_dst_rdy;
    end generate;

    -- =========================================================================
    --  TX MFB RECONFIGURATOR
    -- =========================================================================

    tx_mfb_reconf_i : entity work.MFB_RECONFIGURATOR
    generic map(
        RX_REGIONS           => MD_REGIONS,
        RX_REGION_SIZE       => MD_REGION_SIZE,
        RX_BLOCK_SIZE        => MD_BLOCK_SIZE,
        RX_ITEM_WIDTH        => MD_ITEM_WIDTH,
        TX_REGIONS           => TX_REGIONS,
        TX_REGION_SIZE       => TX_REGION_SIZE,
        TX_BLOCK_SIZE        => TX_BLOCK_SIZE,
        TX_ITEM_WIDTH        => TX_ITEM_WIDTH,
        FIFO_SIZE            => 32,
        FRAMES_OVER_TX_BLOCK => 0,
        DEVICE               => DEVICE
    )
    port map(
        CLK        => TX_CLK,
        RESET      => TX_RESET,

        RX_DATA    => cg_mfb_data,
        RX_SOF     => cg_mfb_sof,
        RX_EOF     => cg_mfb_eof,
        RX_SOF_POS => cg_mfb_sof_pos,
        RX_EOF_POS => cg_mfb_eof_pos,
        RX_SRC_RDY => cg_mfb_src_rdy,
        RX_DST_RDY => cg_mfb_dst_rdy,

        TX_DATA    => TX_MFB_DATA,
        TX_SOF     => TX_MFB_SOF,
        TX_EOF     => TX_MFB_EOF,
        TX_SOF_POS => TX_MFB_SOF_POS,
        TX_EOF_POS => TX_MFB_EOF_POS,
        TX_SRC_RDY => TX_MFB_SRC_RDY,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

    -- -------------------------------------------------------------------------
    --  OUTGOING FRAME LOGIC
    -- -------------------------------------------------------------------------
    --  There are no gaps inside frames => OUTGOING_FRAME = TX_MFB_SRC_RDY

    process (TX_CLK)
    begin
        if (rising_edge(TX_CLK)) then
            OUTGOING_FRAME <= TX_MFB_SRC_RDY;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    --  INCOMPLETE FRAME LOGIC - DEBUG ONLY
    -- -------------------------------------------------------------------------

    tx_inc_frame_g : for r in 0 to TX_REGIONS-1 generate
        tx_inc_frame(r+1) <= (TX_MFB_SOF(r) and not TX_MFB_EOF(r) and not tx_inc_frame(r)) or
                          (TX_MFB_SOF(r) and TX_MFB_EOF(r) and tx_inc_frame(r)) or
                          (not TX_MFB_SOF(r) and not TX_MFB_EOF(r) and tx_inc_frame(r));
    end generate;

    process (TX_CLK)
    begin
        if (rising_edge(TX_CLK)) then
            if (TX_RESET = '1') then
                tx_inc_frame(0) <= '0';
            elsif (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                tx_inc_frame(0) <= tx_inc_frame(TX_REGIONS);
            end if;
        end if;
    end process;

    tx_gap_inside_frame_dbg <= tx_inc_frame(0) and not TX_MFB_SRC_RDY;

    process (TX_CLK)
    begin
        if (rising_edge(TX_CLK)) then
            tx_gap_inside_frame_dbg_reg <= tx_gap_inside_frame_dbg;
        end if;
    end process;

    assert (tx_gap_inside_frame_dbg_reg /= '1')
        report "TX_MAC_LITE: Gap inside frame on TX MFB stream!"
        severity failure;

    -- =========================================================================
    --  STATISTICS MODULE
    -- =========================================================================

    process (RX_CLK)
    begin
        if rising_edge(RX_CLK) then
            stat_rx_frame_inc_reg      <= fl_mfb_eof and fl_mfb_src_rdy and fl_mfb_dst_rdy;
            stat_tx_frame_inc_reg      <= fl_mfb_eof and fl_mfb_src_rdy and fl_mfb_dst_rdy and not fl_mfb_discard;
            stat_tx_frame_length_reg   <= fl_mfb_frame_len;
            stat_discard_frame_inc_reg <= fl_mfb_eof and fl_mfb_src_rdy and fl_mfb_dst_rdy and fl_mfb_discard;
        end if;
    end process;

    stat_unit_i : entity work.TX_MAC_LITE_STAT_UNIT
    generic map(
        MFB_REGIONS        => MD_REGIONS,
        LENGTH_WIDTH       => LEN_WIDTH,
        DEVICE             => DEVICE,
        USE_DSP_CNT        => USE_DSP_CNT,
        FRAME_LEN_WITH_CRC => RX_INCLUDE_CRC
    )
    port map(
        CLK                         => RX_CLK,
        RESET                       => RX_RESET,

        CTRL_STROBE_CNT             => ctrl_strobe_cnt,
        CTRL_RESET_CNT              => ctrl_reset_cnt,

        VECTOR_INC_TOTAL_FRAMES     => stat_rx_frame_inc_reg,
        VECTOR_INC_SENT_FRAMES      => stat_tx_frame_inc_reg,
        VECTOR_INC_DISCARDED        => stat_discard_frame_inc_reg,

        FRAME_LENGTH                => stat_tx_frame_length_reg,
        FRAME_LENGTH_VLD            => stat_tx_frame_inc_reg,

        STAT_TOTAL_FRAMES           => stat_total_frames,
        STAT_TOTAL_SENT_FRAMES      => stat_total_sent_frames,
        STAT_TOTAL_SENT_OCTECTS     => stat_total_sent_octects,
        STAT_TOTAL_DISCARDED_FRAMES => stat_total_discarded_frames
    );

    -- =========================================================================
    --  MI32 ADDRESS DECODER MODULE
    -- =========================================================================

    adc_i : entity work.TX_MAC_LITE_ADDR_DEC
    generic map(
        CRC_INSERTION_EN => CRC_GEN,
        DEVICE           => DEVICE
    )
    port map(
        CLK                         => RX_CLK,
        RESET                       => RX_RESET,

        MI_CLK                      => MI_CLK,
        MI_RESET                    => MI_RESET,
        MI_DWR                      => MI_DWR,
        MI_ADDR                     => MI_ADDR,
        MI_RD                       => MI_RD,
        MI_WR                       => MI_WR,
        MI_BE                       => MI_BE,
        MI_DRD                      => MI_DRD,
        MI_ARDY                     => MI_ARDY,
        MI_DRDY                     => MI_DRDY,

        STAT_TOTAL_FRAMES           => stat_total_frames,
        STAT_TOTAL_SENT_FRAMES      => stat_total_sent_frames,
        STAT_TOTAL_SENT_OCTECTS     => stat_total_sent_octects,
        STAT_TOTAL_DISCARDED_FRAMES => stat_total_discarded_frames,

        CTRL_STROBE_CNT             => ctrl_strobe_cnt,
        CTRL_RESET_CNT              => ctrl_reset_cnt,
        CTRL_OBUF_EN                => ctrl_obuf_en
    );

end architecture;
