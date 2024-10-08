-- frame_packer.vhd: Unit for merging small MFB packets into SuperPacket
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): David Beneš <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The FRAME_PACKER module is used to create Super-Packets. The incoming packets are aligned to the
-- BLOCKs so that the space between them is minimal (ranges from 0 to 7 items per each packet). The
-- size of the Super-Packet is set by the parameter SPKT_SIZE_MIN. This value is used for length
-- comparison, so the super-packet size should be around this length. The timeout is set by the
-- parameter TIMEOUT_CLK_NO, e.g. in number of clock cycles. In the worst case, the latency is
-- 2*TIMEOUT_CLK_NO due to the internal arrangement. The TX_MVB_HDR_META and TX_MVB_DISCARD are
-- included here for compatibility, but are not currently used. The depth of each channel FIFO is
-- set by the constant value FIFO_DEPTH and is set by deafult to 512 (Best BRAM optimization for Intel).
-- Warning! There is a possible bug when sending the combination of small and large packets. In 400G
-- version this could result in sending a packet larger than USR_PKT_SIZE_MAX.
--
entity FRAME_PACKER is
    generic(
        -- Number of regions for incoming and outgoing packets. Note that the 4 region version is not resource optimized and will most likely not fit in the FPGA.
        MFB_REGIONS         : natural := 4;
        -- Number of blocks in each region for incoming and outgoing packets. Only this configuration was tested.
        MFB_REGION_SIZE     : natural := 8;
        -- Number of items in each block for incoming and outgoing packets. Only this configuration was tested.
        MFB_BLOCK_SIZE      : natural := 8;
        -- Length of each item in bits for incoming and outgoing packets. Only this configuration was tested.
        MFB_ITEM_WIDTH      : natural := 8;
        -- Number of virtual lanes. This number should be a power of 2. Note that each channel is created as a standalone unit (resource usage is exponentially dependent on this parameter).
        RX_CHANNELS         : natural := 8;
        -- Header meta is not currently used.
        HDR_META_WIDTH      : natural := 12;
        -- Minimal size in bytes of the incoming packets (also minimal size of Super-Packet).
        USR_RX_PKT_SIZE_MIN : natural := 64;
        -- Maximal size in bytes of the incoming packets (also maximal size of Super-Packet).
        USR_RX_PKT_SIZE_MAX : natural := 2**14;
        -- The size of the Super-Packet (in bytes) the component is trying to reach. Should be power of 2.
        SPKT_SIZE_MIN       : natural := 2**13;
        -- Timeout in clock cycles. Should be power of 2.
        TIMEOUT_CLK_NO      : natural := 4096;
        -- Optimization for FIFOs
        DEVICE              : string := "AGILEX"
    );
    port(
        -- =========================================================================
        -- Clock and Resets inputs
        -- =========================================================================
        CLK : in std_logic;
        RST : in std_logic;

        -- =========================================================================
        -- RX MFB+MVB interface (regular packets)
        -- =========================================================================
        RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY  : in  std_logic;
        RX_MFB_DST_RDY  : out std_logic;

        -- Length of the regular packets
        RX_MVB_LEN      : in  std_logic_vector(MFB_REGIONS*log2(USR_RX_PKT_SIZE_MAX+1) - 1 downto 0);
        -- Channel ID of each regular packet
        RX_MVB_CHANNEL  : in  std_logic_vector(MFB_REGIONS*max(1,log2(RX_CHANNELS))-1 downto 0);
        RX_MVB_VLD      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        -- =========================================================================
        --  TX MFB+MVB interface (Super-Packets)
        -- =========================================================================
        TX_MFB_DATA     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY  : out std_logic;
        TX_MFB_DST_RDY  : in  std_logic;

        -- Length of the Super-Packet
        TX_MVB_LEN      : out std_logic_vector(MFB_REGIONS*log2(USR_RX_PKT_SIZE_MAX+1)-1 downto 0);
        -- Not used
        TX_MVB_HDR_META : out std_logic_vector(MFB_REGIONS*HDR_META_WIDTH-1 downto 0);
        -- Not used
        TX_MVB_DISCARD  : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Channel ID of each Super-Packet
        TX_MVB_CHANNEL  : out std_logic_vector(MFB_REGIONS*max(1,log2(RX_CHANNELS))-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of FRAME_PACKER is
    ------------------------------------------------------------
    --              CONSTANT DECLARATION                      --
    ------------------------------------------------------------
    constant MVB_LEN_WIDTH              : natural := log2(USR_RX_PKT_SIZE_MAX+1);
    constant MVB_HDR_META_WIDTH         : natural := HDR_META_WIDTH;
    constant MVB_CHANNEL_WIDTH          : natural := log2(RX_CHANNELS);
    constant MVB_DISCARD_WIDTH          : natural := 1;

    constant MVB_ITEM_WIDTH             : natural := MVB_LEN_WIDTH + MVB_HDR_META_WIDTH + MVB_CHANNEL_WIDTH + MVB_DISCARD_WIDTH;
    constant WORD_SIZE                  : natural := (MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/8;

    -- Depth of FIFO in each channel
    constant FIFO_DEPTH                 : natural := max(512, ((USR_RX_PKT_SIZE_MAX/WORD_SIZE)*2));

    -- Equal to the number of possible packets in MFB word
    constant MUX_WIDTH                  : natural := MFB_REGIONS + 1;

    -- Output MVB FIFO
    constant MVB_FIFO_ITEMS             : natural := 512;

    ------------------------------------------------------------
    --                  SUBTYPE DECLARATION                   --
    ------------------------------------------------------------
    subtype MVB_LEN_SLICE           is natural range MVB_ITEM_WIDTH - 1 downto MVB_HDR_META_WIDTH + MVB_CHANNEL_WIDTH + MVB_DISCARD_WIDTH;
    subtype MVB_HDR_META_SLICE      is natural range MVB_ITEM_WIDTH - MVB_LEN_WIDTH - 1 downto MVB_CHANNEL_WIDTH + MVB_DISCARD_WIDTH;
    subtype MVB_CHANNEL_SLICE       is natural range MVB_ITEM_WIDTH - MVB_LEN_WIDTH - MVB_HDR_META_WIDTH -1 downto MVB_DISCARD_WIDTH;
    subtype MVB_DISCARD_SLICE       is natural range MVB_ITEM_WIDTH - MVB_LEN_WIDTH - MVB_HDR_META_WIDTH - MVB_CHANNEL_WIDTH - 1 downto 0;

    subtype MFB_BLOCK_RANGE         is natural range MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1  downto 0;
    subtype MFB_EOF_BLOCK_SLICE     is natural range max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) - max(1,log2(MFB_REGION_SIZE));

    ------------------------------------------------------------
    --                  SIGNAL DECLARATION                    --
    ------------------------------------------------------------
    -- Metadata insertor
    signal mvb_len_arr                  : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(USR_RX_PKT_SIZE_MAX+1) - 1 downto 0);
    signal mvb_channel_arr              : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1,log2(RX_CHANNELS))-1 downto 0);
    signal mvb_data_arr                 : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(USR_RX_PKT_SIZE_MAX+1) + max(1,log2(RX_CHANNELS)) - 1 downto 0);

    signal tx_mins_data                 : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal tx_mins_mvb                  : std_logic_vector(MFB_REGIONS*(log2(USR_RX_PKT_SIZE_MAX+1) + max(1,log2(RX_CHANNELS))) - 1 downto 0);
    signal tx_mins_sof                  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_mins_eof                  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_mins_sof_pos              : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal tx_mins_eof_pos              : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal tx_mins_src_rdy              : std_logic;
    signal tx_mins_dst_rdy              : std_logic;

    -- Auxiliary generator
    signal aux_tx_block_vld             : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal aux_tx_sof_one_hot           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal aux_tx_eof_one_hot           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal aux_tx_sof_pos_bs            : slv_array_t(MFB_REGIONS downto 0)(max(1, log2(MFB_REGION_SIZE))-1 downto 0);
    signal aux_tx_pkt_lng               : slv_array_t(MFB_REGIONS downto 0)(max(1, log2(USR_RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    signal aux_tx_channel_bs            : slv_array_t(MFB_REGIONS downto 0)(max(1,log2(RX_CHANNELS)) - 1 downto 0);

    signal aux_tx_mfb_data              : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal aux_tx_mfb_src_rdy           : std_logic_vector(MFB_REGIONS downto 0);
    signal aux_tx_mfb_dst_rdy           : std_logic;

    signal aux_rx_src_rdy               : std_logic;
    signal aux_rx_dst_rdy               : std_logic;

    -- BS_CTRL
    signal bs_ctrl_tx_sel               : slv_array_t(MFB_REGIONS downto 0)(max(1, log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
    signal bs_ctrl_tx_ptr_inc           : u_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) + 1 - 1 downto 0);
    signal bs_ctrl_tx_src_rdy           : std_logic_vector(RX_CHANNELS - 1 downto 0);
    -- Select signal for demux
    signal bs_ctrl_tx_channel_bs        : slv_array_t(MFB_REGIONS downto 0)(max(1,log2(RX_CHANNELS)) - 1 downto 0);

    -- Channel Pointers
    signal ch_ptr_tx_ch_ptr             : u_array_t(RX_CHANNELS - 1 downto 0)(max(1,log2(MFB_REGIONS*MFB_REGION_SIZE)) - 1 downto 0);
    signal ch_ptr_tx_ch_overflow        : std_logic_vector(RX_CHANNELS - 1 downto 0);

    -- BS_PER_PACKET
    signal bs_per_pkt_tx_data           : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal bs_per_pkt_tx_pkt_lng        : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(USR_RX_PKT_SIZE_MAX+1))- 1 downto 0);
    signal bs_per_pkt_tx_block_vld      : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal bs_per_pkt_tx_sof_one_hot    : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal bs_per_pkt_tx_eof_one_hot    : slv_array_t(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    -- CH_DEMUX
    signal ch_demux_tx_data             : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal ch_demux_tx_pkt_lng          : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(USR_RX_PKT_SIZE_MAX+1)) - 1 downto 0);
    signal ch_demux_tx_block_vld        : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal ch_demux_tx_sof_one_hot      : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);
    signal ch_demux_tx_eof_one_hot      : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS downto 0)(MFB_REGIONS*MFB_REGION_SIZE - 1 downto 0);

    -- DMA_CHANNEL
    signal dma_ch_tx_data               : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal dma_ch_tx_pkt_len            : slv_array_t(RX_CHANNELS - 1 downto 0)(log2(USR_RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal dma_ch_tx_sof                : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_ch_tx_eof                : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS-1 downto 0);
    signal dma_ch_tx_sof_pos            : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal dma_ch_tx_eof_pos            : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal dma_ch_tx_src_rdy            : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal dma_ch_tx_dst_rdy            : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal dma_ch_tx_ch_meta            : slv_array_2d_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS - 1 downto 0)(max(1,log2(RX_CHANNELS)) +  log2(USR_RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    signal dma_ch_tx_ch_meta_slv        : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS*(max(1,log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1)) - 1 downto 0);
    signal dma_ch_tx_stop               : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal dma_ch_tx_stop_std           : std_logic;

    -- Concatenate
    signal conc_tx_data                 : slv_array_t(MFB_REGIONS downto 0)((MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE+MFB_REGIONS*MFB_REGION_SIZE*max(1, log2(USR_RX_PKT_SIZE_MAX + 1)) - 1 downto 0);

    -- Merger
    signal tx_merger_meta               : std_logic_vector(MFB_REGIONS*(max(1, log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1) ) - 1 downto 0);

    -- MVB_FIFO
    signal mvb_hdr_full                 : std_logic;
    signal mvb_hdr_empty                : std_logic;
    signal mvb_hdr_status               : std_logic_vector(log2(MVB_FIFO_ITEMS) downto 0);

    signal tx_mvb_data                  : std_logic_vector(MFB_REGIONS*(max(1, log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX + 1)) - 1 downto 0);
    signal tx_mvb_data_arr              : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1) - 1 downto 0);
    signal tx_mvb_channel_arr           : slv_array_t(MFB_REGIONS - 1 downto 0)(max(1, log2(RX_CHANNELS)) - 1 downto 0);
    signal tx_mvb_len_arr               : slv_array_t(MFB_REGIONS - 1 downto 0)(log2(USR_RX_PKT_SIZE_MAX+1)  - 1 downto 0);

    -- Verification module
    signal ver_eof                      : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal ver_last                     : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal ver_vld                      : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal ver_src_rdy                  : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal ver_dst_rdy                  : std_logic_vector(RX_CHANNELS - 1 downto 0);

    signal debug_pkt_num                : slv_array_t(RX_CHANNELS - 1 downto 0)(max(1, log2(MFB_REGIONS*FIFO_DEPTH)) - 1 downto 0);
    signal debug_pkt_num_src_rdy        : std_logic_vector(RX_CHANNELS - 1 downto 0);

    signal debug_eof                    : slv_array_t(RX_CHANNELS - 1 downto 0)(MFB_REGIONS - 1 downto 0);
    signal debug_eof_src_rdy            : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal debug_sp_eof                 : std_logic_vector(RX_CHANNELS - 1 downto 0);
    signal debug_sp_eof_src_rdy         : std_logic_vector(RX_CHANNELS - 1 downto 0);

    signal pkt_cnt_debug                : unsigned(30 downto 0);
    signal sp_pkt_cnt_debug             : unsigned(30 downto 0);

begin
    ------------------------------------------------------------
    --                  Packet Counter [DEBUG]                --
    ------------------------------------------------------------
    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                pkt_cnt_debug   <= (others => '0');
            elsif (RX_MFB_SRC_RDY = '1' and RX_MFB_DST_RDY = '1') then
                pkt_cnt_debug   <= pkt_cnt_debug + to_unsigned(count_ones(RX_MFB_SOF), pkt_cnt_debug'length);
            end if;
        end if;
    end process;

    process(all)
    begin
        if rising_edge(CLK) then
            if RST = '1' then
                sp_pkt_cnt_debug   <= (others => '0');
            elsif (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                sp_pkt_cnt_debug   <= sp_pkt_cnt_debug + to_unsigned(count_ones(TX_MFB_SOF), sp_pkt_cnt_debug'length);
            end if;
        end if;
    end process;

    ------------------------------------------------------------
    --                   METADATA INSERTOR                    --
    ------------------------------------------------------------
    mvb_len_arr         <= slv_array_deser(RX_MVB_LEN, MFB_REGIONS);
    mvb_channel_arr     <=slv_array_deser(RX_MVB_CHANNEL, MFB_REGIONS);

    metadata_insertion_g: for r in 0 to MFB_REGIONS - 1 generate
        mvb_data_arr(r) <= mvb_len_arr(r) & mvb_channel_arr(r);
    end generate;

    -- Synchronization of MVB and MFB data
    metadata_insertor_i: entity work.METADATA_INSERTOR
        generic map(
            MVB_ITEMS       => MFB_REGIONS,
            MVB_ITEM_WIDTH  => log2(USR_RX_PKT_SIZE_MAX+1) + max(1,log2(RX_CHANNELS)),
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            INSERT_MODE     => 0,
            MVB_FIFO_SIZE   => 64,
            DEVICE          => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RST,

            -- [Length][Channel]
            RX_MVB_DATA     => slv_array_ser(mvb_data_arr),
            RX_MVB_VLD      => RX_MVB_VLD,
            RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

            RX_MFB_DATA     => RX_MFB_DATA,
            RX_MFB_META     => (others => '0'),
            RX_MFB_SOF      => RX_MFB_SOF,
            RX_MFB_EOF      => RX_MFB_EOF,
            RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
            RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
            RX_MFB_SRC_RDY  => RX_MFB_SRC_RDY,
            RX_MFB_DST_RDY  => RX_MFB_DST_RDY,

            TX_MFB_DATA     => tx_mins_data,
            TX_MFB_META     => open,
            TX_MFB_META_NEW => tx_mins_mvb,
            TX_MFB_SOF      => tx_mins_sof,
            TX_MFB_EOF      => tx_mins_eof,
            TX_MFB_SOF_POS  => tx_mins_sof_pos,
            TX_MFB_EOF_POS  => tx_mins_eof_pos,
            TX_MFB_SRC_RDY  => tx_mins_src_rdy,
            TX_MFB_DST_RDY  => tx_mins_dst_rdy
    );

    ------------------------------------------------------------
    --                    STOP INTERPRETER                    --
    ------------------------------------------------------------
    -- STOP signal from each DMA Cell
    -- STOP signal can be registerd if needed
    dma_ch_tx_stop_std  <= or (dma_ch_tx_stop);
    tx_mins_dst_rdy     <= aux_rx_dst_rdy and (not dma_ch_tx_stop_std);
    aux_rx_src_rdy      <= tx_mins_src_rdy and (not dma_ch_tx_stop_std);

    ------------------------------------------------------------
    --                     AUX GENERATOR                      --
    ------------------------------------------------------------
    -- Generates signals necessary for the proper functioning of the following parts
    aux_gen_i: entity work.FP_AUX_GEN
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            META_WIDTH          => log2(USR_RX_PKT_SIZE_MAX+1) + max(1,log2(RX_CHANNELS)),

            RX_CHANNELS         => RX_CHANNELS,
            RX_PKT_SIZE_MAX     => USR_RX_PKT_SIZE_MAX
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_MFB_DATA     => tx_mins_data,
            RX_MFB_META     => tx_mins_mvb,
            RX_MFB_SOF      => tx_mins_sof,
            RX_MFB_EOF      => tx_mins_eof,
            RX_MFB_SOF_POS  => tx_mins_sof_pos,
            RX_MFB_EOF_POS  => tx_mins_eof_pos,
            RX_MFB_SRC_RDY  => aux_rx_src_rdy,
            RX_MFB_DST_RDY  => aux_rx_dst_rdy,

            TX_MFB_DATA     => aux_tx_mfb_data,
            TX_MFB_SRC_RDY  => aux_tx_mfb_src_rdy,
            TX_MFB_DST_RDY  => aux_tx_mfb_dst_rdy,

            TX_CHANNEL_BS   => aux_tx_channel_bs,
            TX_PKT_LNG      => aux_tx_pkt_lng,
            TX_BLOCK_VLD    => aux_tx_block_vld,
            TX_SOF_ONE_HOT  => aux_tx_sof_one_hot,
            TX_EOF_ONE_HOT  => aux_tx_eof_one_hot,
            TX_SOF_POS_BS   => aux_tx_sof_pos_bs
    );

    ------------------------------------------------------------
    --                          BS CTRL                       --
    ------------------------------------------------------------
    -- Generates select signal for BSs and increment for each channel pointer
    bs_ctrl_i: entity work.FP_BS_CTRL
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_CHANNELS         => RX_CHANNELS
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_BLOCK_VLD    => aux_tx_block_vld,
            RX_SOF_POS_BS   => aux_tx_sof_pos_bs,
            RX_CH_PTR       => ch_ptr_tx_ch_ptr,
            RX_SRC_RDY      => or aux_tx_mfb_src_rdy,
            RX_CHANNEL_BS   => aux_tx_channel_bs,

            TX_SEL          => bs_ctrl_tx_sel,
            TX_PTR_INC      => bs_ctrl_tx_ptr_inc,
            TX_SRC_RDY      => bs_ctrl_tx_src_rdy,
            TX_CHANNEL_BS   => bs_ctrl_tx_channel_bs
    );

    ------------------------------------------------------------
    --                       CH PTR                           --
    ------------------------------------------------------------
    -- Keeps track of the status of each TMP_REG
    ch_ptr_g: for i in 0 to RX_CHANNELS - 1 generate
        ch_ptr_i: entity work.FP_PTR_CTRL
            generic map(
                MFB_REGIONS         => MFB_REGIONS,
                MFB_REGION_SIZE     => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH
            )
            port map(
                CLK => CLK,
                RST => RST,

                RX_SRC_RDY      => bs_ctrl_tx_src_rdy(i),
                RX_PTR_INC      => bs_ctrl_tx_ptr_inc(i),

                TX_CH_PTR       => ch_ptr_tx_ch_ptr(i),
                TX_CH_OVERFLOW  => ch_ptr_tx_ch_overflow(i)
        );
    end generate;

    ------------------------------------------------------------
    --                     CONCATENATE                        --
    ------------------------------------------------------------
    -- Concatenation of DATA with auxiliary signals - these are shifted with the data
    packet_concatenate_i: entity work.FP_META_CONCATENATE
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_PKT_SIZE_MAX     => USR_RX_PKT_SIZE_MAX
        )
        port map(
            RX_MFB_DATA     => aux_tx_mfb_data,
            RX_BLOCK_VLD    => aux_tx_block_vld,
            RX_SOF_ONE_HOT  => aux_tx_sof_one_hot,
            RX_EOF_ONE_HOT  => aux_tx_eof_one_hot,
            RX_PKT_LNG      => aux_tx_pkt_lng,
            TX_DATA_CONC    => conc_tx_data
    );

    ------------------------------------------------------------
    --                     BS PER PACKET                      --
    ------------------------------------------------------------
    -- Encapsulation of BSs and data extraction
    bs_per_packet_i: entity work.FP_BS_PER_PACKET
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_PKT_SIZE_MAX     => USR_RX_PKT_SIZE_MAX
        )
        port map(
            CLK             => CLK,
            RX_DATA         => conc_tx_data,
            RX_SEL          => bs_ctrl_tx_sel,

            TX_DATA         => bs_per_pkt_tx_data,
            TX_BLOCK_VLD    => bs_per_pkt_tx_block_vld,
            TX_SOF_ONE_HOT  => bs_per_pkt_tx_sof_one_hot,
            TX_EOF_ONE_HOT  => bs_per_pkt_tx_eof_one_hot,
            TX_PKT_LNG      => bs_per_pkt_tx_pkt_lng
    );

    ------------------------------------------------------------
    --                    CHANNEL DEMUX                       --
    ------------------------------------------------------------
    -- Demultiplexer - routes data to correct Channel Cell
    ch_demux_i: entity work.FP_CHANNEL_DEMUX
        generic map(
            MFB_REGIONS         => MFB_REGIONS,
            MFB_REGION_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
            RX_CHANNELS         => RX_CHANNELS,
            RX_PKT_SIZE_MAX     => USR_RX_PKT_SIZE_MAX
        )
        port map(
            RX_CHANNEL_BS   => bs_ctrl_tx_channel_bs,

            RX_DATA         => bs_per_pkt_tx_data,
            RX_PKT_LNG      => bs_per_pkt_tx_pkt_lng,
            RX_BLOCK_VLD    => bs_per_pkt_tx_block_vld,
            RX_SOF_ONE_HOT  => bs_per_pkt_tx_sof_one_hot,
            RX_EOF_ONE_HOT  => bs_per_pkt_tx_eof_one_hot,

            TX_DATA         => ch_demux_tx_data,
            TX_BLOCK_VLD    => ch_demux_tx_block_vld,
            TX_SOF_ONE_HOT  => ch_demux_tx_sof_one_hot,
            TX_EOF_ONE_HOT  => ch_demux_tx_eof_one_hot,
            TX_PKT_LNG      => ch_demux_tx_pkt_lng
    );

    ------------------------------------------------------------
    --                      FP CHANNELS                       --
    ------------------------------------------------------------
    -- This entity encapsulates components for handling shifted data
    dma_channel_g: for i in 0 to RX_CHANNELS - 1 generate
        dma_channel_i: entity work.FP_CHANNEL
            generic map(
                MFB_REGIONS         => MFB_REGIONS,
                MFB_REGION_SIZE     => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH,
                MUX_WIDTH           => MUX_WIDTH,
                FIFO_DEPTH          => FIFO_DEPTH,
                TIMEOUT_CLK_NO      => TIMEOUT_CLK_NO,
                DEVICE              => DEVICE,
                RX_PKT_SIZE_MIN     => SPKT_SIZE_MIN,
                RX_PKT_SIZE_MAX     => USR_RX_PKT_SIZE_MAX
            )
            port map(
                CLK => CLK,
                RST => RST,

                DEBUG_PKT_NUM           => debug_pkt_num(i),
                DEBUG_PKT_NUM_SRC_RDY   => debug_pkt_num_src_rdy(i),

                DEBUG_EOF               => debug_eof(i),
                DEBUG_EOF_SRC_RDY       => debug_eof_src_rdy(i),
                DEBUG_SP_EOF            => debug_sp_eof(i),
                DEBUG_SP_EOF_SRC_RDY    => debug_sp_eof_src_rdy(i),

                RX_TMP_PTR_UNS  => ch_ptr_tx_ch_ptr(i),
                RX_TMP_OVERFLOW => ch_ptr_tx_ch_overflow(i),

                RX_DATA         => ch_demux_tx_data(i),
                RX_PKT_LNG      => ch_demux_tx_pkt_lng(i),
                RX_BLOCK_VLD    => ch_demux_tx_block_vld(i),
                RX_SOF_ONE_HOT  => ch_demux_tx_sof_one_hot(i),
                RX_EOF_ONE_HOT  => ch_demux_tx_eof_one_hot(i),

                TX_DATA         => dma_ch_tx_data(i),
                TX_PKT_LNG      => dma_ch_tx_pkt_len(i),
                TX_SOF          => dma_ch_tx_sof(i),
                TX_EOF          => dma_ch_tx_eof(i),
                TX_SOF_POS      => dma_ch_tx_sof_pos(i),
                TX_EOF_POS      => dma_ch_tx_eof_pos(i),
                TX_SRC_RDY      => dma_ch_tx_src_rdy(i),
                TX_DST_RDY      => dma_ch_tx_dst_rdy(i),

                -- Stop signal -- can be registered as needed
                TX_STOP         => dma_ch_tx_stop(i)
        );

        -- Channel & PKT_LEN
        channel_per_region_g: for r in 0 to MFB_REGIONS - 1 generate
            dma_ch_tx_ch_meta(i)(r) <= std_logic_vector(to_unsigned(i, max(1,log2(RX_CHANNELS)))) & dma_ch_tx_pkt_len(i);
        end generate;
    end generate;

    channel_conc_g: for ch in 0 to RX_CHANNELS - 1 generate
        dma_ch_tx_ch_meta_slv(ch) <= slv_array_ser(dma_ch_tx_ch_meta(ch));
    end generate;

    ------------------------------------------------------------
    --                          MERGER                        --
    ------------------------------------------------------------
    -- Merger combines outputs of DMA Cells to the single interface
    merger_i: entity work.FP_MERGER
        generic map(
            -- MFB parameters
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REGION_SIZE => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            MFB_META_WIDTH  => max(1,log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1) ,

            MERGER_INPUTS       => RX_CHANNELS,
            DEVICE              => DEVICE
        )
        port map(
            CLK => CLK,
            RST => RST,

            RX_MFB_DATA    => dma_ch_tx_data,
            RX_MFB_META    => dma_ch_tx_ch_meta_slv,
            RX_MFB_SOF     => dma_ch_tx_sof,
            RX_MFB_EOF     => dma_ch_tx_eof,
            RX_MFB_SOF_POS => dma_ch_tx_sof_pos,
            RX_MFB_EOF_POS => dma_ch_tx_eof_pos,
            RX_MFB_SRC_RDY => dma_ch_tx_src_rdy,
            RX_MFB_DST_RDY => dma_ch_tx_dst_rdy,

            TX_MFB_DATA    => TX_MFB_DATA,
            TX_MFB_META    => tx_merger_meta,
            TX_MFB_SOF     => TX_MFB_SOF,
            TX_MFB_EOF     => TX_MFB_EOF,
            TX_MFB_SOF_POS => TX_MFB_SOF_POS,
            TX_MFB_EOF_POS => TX_MFB_EOF_POS,
            TX_MFB_SRC_RDY => TX_MFB_SRC_RDY,
            TX_MFB_DST_RDY => TX_MFB_DST_RDY
    );

    ------------------------------------------------------------
    --                       MVB FIFO                         --
    ------------------------------------------------------------
    -- MVB FIFO - Helps meet the strict synchronization requirements of UVM
    mvb_hdr_fifo_i: entity work.MVB_FIFO
        generic map(
          ITEMS          => MFB_REGIONS,
          ITEM_WIDTH     => max(1, log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1) ,
          FIFO_ITEMS     => MVB_FIFO_ITEMS
        )
        port map(
          CLK   => CLK,
          RESET => RST,

          RX_DATA       => tx_merger_meta,
          RX_VLD        => TX_MFB_SOF,
          RX_SRC_RDY    => TX_MFB_SRC_RDY and TX_MFB_DST_RDY and (or (TX_MFB_SOF)),
          RX_DST_RDY    => open,

          -- Channel & PKT_LEN
          TX_DATA       => tx_mvb_data,
          TX_VLD        => TX_MVB_VLD,
          TX_SRC_RDY    => TX_MVB_SRC_RDY,
          TX_DST_RDY    => TX_MVB_DST_RDY,

          LSTBLK         => open,
          FULL           => mvb_hdr_full,
          EMPTY          => mvb_hdr_empty,
          STATUS         => mvb_hdr_status
    );

    tx_mvb_data_arr <= slv_array_deser(tx_mvb_data, MFB_REGIONS);
    mvb_extraction_g: for r in 0 to MFB_REGIONS - 1 generate
        tx_mvb_channel_arr(r)   <= tx_mvb_data_arr(r)(max(1, log2(RX_CHANNELS)) + log2(USR_RX_PKT_SIZE_MAX+ 1)  - 1 downto log2(USR_RX_PKT_SIZE_MAX+ 1) );
        tx_mvb_len_arr(r)       <= tx_mvb_data_arr(r)(log2(USR_RX_PKT_SIZE_MAX+ 1)  - 1 downto 0);
    end generate;

    TX_MVB_CHANNEL  <= slv_array_ser(tx_mvb_channel_arr);
    TX_MVB_LEN      <= slv_array_ser(tx_mvb_len_arr);

    TX_MVB_HDR_META     <= (others => '1');
    TX_MVB_DISCARD      <= (others => '0');

    ------------------------------------------------------------
    --                   VERIFICATION MODULE                  --
    ------------------------------------------------------------
    -- The verification module helps with the verification of SuperPacket boundaries and timeout
    ver_mod_g: for i in 0 to RX_CHANNELS - 1 generate
        ver_mod_i: entity work.FP_VER_MOD
            generic map(
                MFB_REGIONS     => MFB_REGIONS,
                MFB_REGION_SIZE => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,

                FIFO_DEPTH          => FIFO_DEPTH,
                USR_RX_PKT_SIZE_MAX => USR_RX_PKT_SIZE_MAX,
                USR_RX_PKT_SIZE_MIN => USR_RX_PKT_SIZE_MIN
            )
            port map(
                CLK             => CLK,
                RST             => RST,
                RX_READ_EN      => TX_MFB_SRC_RDY,

                RX_PKT_NUM          => debug_pkt_num(i),
                RX_PKT_NUM_SRC_RDY  => debug_pkt_num_src_rdy(i),

                RX_EOF              => debug_eof(i),
                RX_EOF_SRC_RDY      => debug_eof_src_rdy(i),
                RX_SP_EOF           => debug_sp_eof(i),
                RX_SP_EOF_SRC_RDY   => debug_sp_eof_src_rdy(i),

                VER_EOF         => ver_eof(i),
                VER_LAST        => ver_last(i),
                VER_VLD         => ver_vld(i),
                VER_SRC_RDY     => ver_src_rdy(i),
                VER_DST_RDY     => ver_dst_rdy(i)
        );
    end generate;

end architecture;
