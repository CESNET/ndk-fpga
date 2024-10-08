-- tx_dma_chan_start_stop_ctrl.vhd: controls the acception of packets according to the running state
-- of the DMA channels
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--            David Benes      <xbenes52@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;
use work.dma_hdr_pkg.all;

-- This component controls the acception of incoming frames according to the running state of a
-- specific DMA channel. When channel is stopped, all incoming frames to that channel are dropped.
-- When channel is running, all incoming frames on that channel are accepted and reach the
-- output *USR_MFB_* bus. When a stop request of a channel comes when a frame is received on this
-- channel, the frame is received till its end and all other frames will be dropped. The system
-- works vice versa when a start request comes and a frame is dropped on a single channel.
--
-- .. NOTE::
--    A frame can consist out of multiple smaller frames that are delimited by the DMA header.
--
entity TX_DMA_CHAN_START_STOP_CTRL is
    generic (
        DEVICE : string := "ULTRASCALE";

        -- Total number of DMA Channels within this DMA Endpoint
        CHANNELS : natural := 8;

        -- =========================================================================================
        -- Input PCIe interface parameters
        -- =========================================================================================
        PCIE_MFB_REGIONS     : natural := 2;
        PCIE_MFB_REGION_SIZE : natural := 1;
        PCIE_MFB_BLOCK_SIZE  : natural := 8;
        PCIE_MFB_ITEM_WIDTH  : natural := 32;

        -- =========================================================================================
        -- Others
        -- =========================================================================================
        -- Largest packet (in bytes) which can come out of USR_MFB interface
        PKT_SIZE_MAX : natural := 2**16 - 1;

        DBG_SIGNAL_WIDTH : natural := 4
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- Input PCIe MFB interface
        -- =========================================================================================
        PCIE_MFB_DATA    : in  std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
        PCIE_MFB_META    : in  std_logic_vector(PCIE_MFB_REGIONS*(13 + (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1)-1 downto 0);
        PCIE_MFB_SOF     : in  std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        PCIE_MFB_EOF     : in  std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        PCIE_MFB_SOF_POS : in  std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
        PCIE_MFB_EOF_POS : in  std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
        PCIE_MFB_SRC_RDY : in  std_logic;
        PCIE_MFB_DST_RDY : out std_logic;

        -- =========================================================================================
        -- Output MFB interface
        -- =========================================================================================
        USR_MFB_DATA    : out std_logic_vector(PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH-1 downto 0);
        USR_MFB_META    : out std_logic_vector(PCIE_MFB_REGIONS*((PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1)-1 downto 0);
        USR_MFB_SOF     : out std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        USR_MFB_EOF     : out std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);
        USR_MFB_SOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE)) -1 downto 0);
        USR_MFB_EOF_POS : out std_logic_vector(PCIE_MFB_REGIONS*max(1, log2(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE)) -1 downto 0);
        USR_MFB_SRC_RDY : out std_logic;
        USR_MFB_DST_RDY : in  std_logic;

        -- =========================================================================================
        -- Start/stop interface from the TX_DMA_SW_MANAGER
        -- =========================================================================================
        START_REQ_CHAN : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        START_REQ_VLD  : in  std_logic;
        START_REQ_ACK  : out std_logic;
        STOP_REQ_CHAN  : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        STOP_REQ_VLD   : in  std_logic;
        STOP_REQ_ACK   : out std_logic;

        -- =========================================================================================
        -- Control signals for the counter of discarded packets
        -- =========================================================================================
        PKT_DISC_CHAN  : out std_logic_vector(log2(CHANNELS) -1 downto 0);
        PKT_DISC_INC   : out std_logic;
        PKT_DISC_BYTES : out std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);

        -- =========================================================================================
        -- Debug signals
        -- =========================================================================================
        ST_SP_DBG_CHAN : out std_logic_vector(log2(CHANNELS) -1 downto 0);
        ST_SP_DBG_META : out std_logic_vector(DBG_SIGNAL_WIDTH -1 downto 0)
    );
end entity;

architecture FULL of TX_DMA_CHAN_START_STOP_CTRL is

    constant MFB_LENGTH : natural := PCIE_MFB_REGIONS*PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH;

    -- =============================================================================================
    -- Defining ranges for meta signal
    -- =============================================================================================
    constant META_IS_DMA_HDR_W : natural := 1;
    constant META_PCIE_ADDR_W  : natural := 62;
    constant META_CHAN_NUM_W   : natural := log2(CHANNELS);
    constant META_BE_W         : natural := (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8;
    constant META_BYTE_CNT_W   : natural := 13;

    constant META_IS_DMA_HDR_O : natural := 0;
    constant META_PCIE_ADDR_O  : natural := META_IS_DMA_HDR_O + META_IS_DMA_HDR_W;
    constant META_CHAN_NUM_O   : natural := META_PCIE_ADDR_O + META_PCIE_ADDR_W;
    constant META_BE_O         : natural := META_CHAN_NUM_O + META_CHAN_NUM_W;
    constant META_BYTE_CNT_O   : natural := META_BE_O + META_BE_W;

    subtype META_IS_DMA_HDR   is natural range META_IS_DMA_HDR_O + META_IS_DMA_HDR_W -1 downto META_IS_DMA_HDR_O;
    subtype META_PCIE_ADDR    is natural range   META_PCIE_ADDR_O + META_PCIE_ADDR_W -1 downto META_PCIE_ADDR_O;
    subtype META_CHAN_NUM     is natural range     META_CHAN_NUM_O + META_CHAN_NUM_W -1 downto META_CHAN_NUM_O;
    subtype META_BE           is natural range                 META_BE_O + META_BE_W -1 downto META_BE_O;
    subtype META_BYTE_CNT     is natural range     META_BYTE_CNT_O + META_BYTE_CNT_W -1 downto META_BYTE_CNT_O;

    -- =============================================================================================
    -- State machines' states
    -- =============================================================================================
    type channel_active_state_t is (CHANNEL_RUNNING, CHANNEL_START, CHANNEL_STOP_PENDING, CHANNEL_STOPPED);
    type all_chan_active_states_t is array (CHANNELS -1 downto 0) of channel_active_state_t;
    signal channel_active_pst       : all_chan_active_states_t := (others => CHANNEL_STOPPED);
    signal channel_active_nst       : all_chan_active_states_t := (others => CHANNEL_STOPPED);

    -- MUX inputs to acknowledge start/stop from each channel
    signal chan_start_req_ack       : std_logic_vector(CHANNELS -1 downto 0);
    signal chan_stop_req_ack        : std_logic_vector(CHANNELS -1 downto 0);

    type pkt_acc_state_t is (S_IDLE, S_PKT_PENDING, S_PKT_DROP);
    type all_chan_pkt_acc_state_t is array (CHANNELS -1 downto 0) of pkt_acc_state_t;
    signal pkt_acc_pst              : all_chan_pkt_acc_state_t := (others => S_IDLE);
    signal pkt_acc_nst              : all_chan_pkt_acc_state_t := (others => S_IDLE);

    -- Drop enable for each channel
    signal chan_pkt_drop_en         : slv_array_t(CHANNELS -1 downto 0)(PCIE_MFB_REGIONS -1 downto 0);

    -- MUXed from all channels
    signal pkt_drop_en              : std_logic_vector(PCIE_MFB_REGIONS -1 downto 0);

    -- =============================================================================================
    -- Two regions support
    -- =============================================================================================
    -- This signal is telling us, when the State should change
    -- is_dma_hdr per region
    signal is_dma_hdr_arr       : slv_array_t(CHANNELS - 1 downto 0)(PCIE_MFB_REGIONS - 1 downto 0);

    -- Divide meta signal for better usage
    signal pcie_mfb_meta_arr        : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(13 + (PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1-1 downto 0);

    -- SOF for specific channel
    signal pcie_mfb_sof_arr         : slv_array_t(CHANNELS - 1 downto 0)(PCIE_MFB_REGIONS - 1 downto 0);

    -- Discard logic and statistics
    signal pcie_mfb_data_arr        : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH - 1 downto 0);
    signal pcie_mfb_disc_chan_arr   : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(log2(CHANNELS) -1 downto 0);
    signal pcie_mfb_disc_bytes_arr  : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal pcie_mfb_disc_inc_arr    : std_logic_vector(PCIE_MFB_REGIONS - 1 downto 0);
    signal fifox_mult_di            : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(log2(CHANNELS) + log2(PKT_SIZE_MAX+1) + 1 - 1 downto 0);
    signal fifox_mult_do            : std_logic_vector(log2(CHANNELS) + log2(PKT_SIZE_MAX+1) + 1 - 1 downto 0);
    signal fifox_mult_empty         : std_logic_vector(0 downto 0);

    -- Verification
    signal fifox_mult_full          : std_logic := '0';

    -- Meta extraction
    signal pcie_mfb_meta_ext        : slv_array_t(PCIE_MFB_REGIONS - 1 downto 0)(META_BE_O + META_BE_W -1 downto 0);

    -- =============================================================================================
    -- All things debugging
    -- =============================================================================================
    signal dma_hdr_out_of_order_chan : std_logic_vector(CHANNELS -1 downto 0);
    signal dma_frame_lng_correct     : std_logic_vector(CHANNELS -1 downto 0);
    signal dma_frame_lng_incorrect   : std_logic_vector(CHANNELS -1 downto 0);

    signal tr_byte_lng_stored : u_array_t(CHANNELS -1 downto 0)(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal tr_byte_lng_curr   : u_array_t(CHANNELS -1 downto 0)(log2(PKT_SIZE_MAX+1) -1 downto 0);

    -- attribute mark_debug                       : string;
    -- attribute mark_debug of channel_active_pst : signal is "true";
    -- attribute mark_debug of pkt_acc_pst        : signal is "true";
    -- attribute mark_debug of chan_start_req_ack : signal is "true";
    -- attribute mark_debug of chan_stop_req_ack  : signal is "true";

    -- attribute mark_debug of dma_hdr_out_of_order_chan : signal is "true";
    -- attribute mark_debug of chan_pkt_drop_en          : signal is "true";

    signal meta_is_dma_hdr_int : std_logic_vector(META_IS_DMA_HDR);
    signal meta_pcie_addr_int  : std_logic_vector(META_PCIE_ADDR);
    signal meta_chan_num_int   : std_logic_vector(META_CHAN_NUM);

    -- attribute mark_debug of PCIE_MFB_DATA       : signal is "true";
    -- attribute mark_debug of meta_is_dma_hdr_int : signal is "true";
    -- attribute mark_debug of meta_pcie_addr_int  : signal is "true";
    -- attribute mark_debug of meta_chan_num_int   : signal is "true";
    -- attribute mark_debug of PCIE_MFB_SOF        : signal is "true";
    -- attribute mark_debug of PCIE_MFB_EOF        : signal is "true";
    -- attribute mark_debug of PCIE_MFB_SOF_POS    : signal is "true";
    -- attribute mark_debug of PCIE_MFB_EOF_POS    : signal is "true";
    -- attribute mark_debug of PCIE_MFB_SRC_RDY    : signal is "true";
    -- attribute mark_debug of PCIE_MFB_DST_RDY    : signal is "true";

    signal stop_req_while_pending                       : std_logic_vector(CHANNELS -1 downto 0);
    signal stop_req_while_pending_ored                  : std_logic;
    -- attribute mark_debug of stop_req_while_pending      : signal is "true";
    -- attribute mark_debug of stop_req_while_pending_ored : signal is "true";

    -- attribute mark_debug of ST_SP_DBG_META : signal is "true";

begin
    -- Debug signal for one region
    stop_req_while_pending_ored <= or stop_req_while_pending;
    meta_is_dma_hdr_int         <= PCIE_MFB_META(META_IS_DMA_HDR);
    meta_pcie_addr_int          <= PCIE_MFB_META(META_PCIE_ADDR);
    meta_chan_num_int           <= PCIE_MFB_META(META_CHAN_NUM);

    -- =============================================================================================
    -- Channel start/stop control
    -- =============================================================================================
    channel_active_fsm_g : for j in (CHANNELS -1) downto 0 generate

        stop_req_while_pending(j) <= '1' when (
            pkt_acc_pst(j) = S_PKT_PENDING
            and STOP_REQ_VLD = '1'
            and std_logic_vector(to_unsigned(j, log2(CHANNELS))) = STOP_REQ_CHAN
            ) else '0';

        channel_active_state_reg_p : process (CLK) is
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    channel_active_pst(j) <= CHANNEL_STOPPED;
                else
                    channel_active_pst(j) <= channel_active_nst(j);
                end if;
            end if;
        end process;

        channel_active_nst_logic_p : process (all) is
        begin
            channel_active_nst(j) <= channel_active_pst(j);
            chan_start_req_ack(j) <= '0';
            chan_stop_req_ack(j)  <= '0';

            case channel_active_pst(j) is
                when CHANNEL_STOPPED =>
                    if (START_REQ_VLD = '1' and j = to_integer(unsigned(START_REQ_CHAN))) then
                        channel_active_nst(j) <= CHANNEL_START;
                    end if;

                when CHANNEL_START =>
                    chan_start_req_ack(j) <= '1';
                    channel_active_nst(j) <= CHANNEL_RUNNING;

                when CHANNEL_RUNNING =>
                    if (STOP_REQ_VLD = '1' and j = to_integer(unsigned(STOP_REQ_CHAN))) then
                        channel_active_nst(j) <= CHANNEL_STOP_PENDING;
                    end if;

                when CHANNEL_STOP_PENDING =>
                    if (pkt_acc_pst(j) = S_IDLE) then
                        chan_stop_req_ack(j)  <= '1';
                        channel_active_nst(j) <= CHANNEL_STOPPED;
                    end if;
            end case;
        end process;
    end generate;

    START_REQ_ACK <= chan_start_req_ack(to_integer(unsigned(START_REQ_CHAN)));
    STOP_REQ_ACK  <= chan_stop_req_ack(to_integer(unsigned(STOP_REQ_CHAN)));

    -- =============================================================================================
    -- Channel Select
    -- =============================================================================================
    -- This process creates a channel enable signal for multiple regions
    -- This process sets several (2) state machines in motion at the same time

    -- Possibilities: SOF(0) SOF(1) HDR(0) HDR(1)  Possible Channels
    -- 1)              0      0      0      0            1 Channel
    -- 2)              0      1      0      0            1 Channel
    -- 3)              0      1      0      1            1 Channel
    -- 4)              1      0      0      0            1 Channel
    -- 5)              1      0      1      0            1 Channel
    -- 6)              1      1      0      0      up to 2 Channels
    -- 7)              1      1      0      1      up to 2 Channels
    -- 8)              1      1      1      0      up to 2 Channels
    -- 9)              1      1      1      1            2 Channels

    pcie_mfb_meta_arr   <= slv_array_deser(PCIE_MFB_META, PCIE_MFB_REGIONS);
    channel_sel_p: process(all)
    begin
        is_dma_hdr_arr      <= (others => (others => '0'));
        pcie_mfb_sof_arr    <= (others => (others => '0'));

        -- Last assignment
        for i in 0 to PCIE_MFB_REGIONS - 1 loop
            if PCIE_MFB_SOF(i) = '1' then
                pcie_mfb_sof_arr(to_integer(unsigned(pcie_mfb_meta_arr(i)(META_CHAN_NUM))))(i)  <= '1';
                is_dma_hdr_arr(to_integer(unsigned(pcie_mfb_meta_arr(i)(META_CHAN_NUM))))(i)    <= pcie_mfb_meta_arr(i)(META_IS_DMA_HDR)(0);
            end if;
        end loop;
    end process;

    -- =============================================================================================
    -- Status of a packet processing on all channels
    --
    -- The PKT_PENDING means there are still incoming PCIe transactions for the current packet.
    -- =============================================================================================
    pkt_region_acc_g: if PCIE_MFB_REGIONS = 1 generate
        acceptor_fsm_g : for j in (CHANNELS -1) downto 0 generate
            pkt_acceptor_state_reg_p : process (CLK) is
            begin
                if (rising_edge(CLK)) then
                    if (RESET = '1') then
                        pkt_acc_pst(j)        <= S_IDLE;
                        tr_byte_lng_stored(j) <= (others => '0');
                    else
                        pkt_acc_pst(j) <= pkt_acc_nst(j);
                        tr_byte_lng_stored(j) <= tr_byte_lng_curr(j);
                    end if;
                end if;
            end process;

            pkt_acceptor_nst_logic_p : process (all) is
            begin
                pkt_acc_nst(j)      <= pkt_acc_pst(j);
                tr_byte_lng_curr(j) <= tr_byte_lng_stored(j);

                chan_pkt_drop_en(j) <= (others => '0');
                dma_frame_lng_correct(j)   <= '0';
                dma_frame_lng_incorrect(j) <= '0';

                case pkt_acc_pst(j) is
                    when S_IDLE =>
                        if (
                            PCIE_MFB_SRC_RDY = '1'
                            and PCIE_MFB_SOF = "1"
                            and PCIE_MFB_META(META_IS_DMA_HDR) = "0"
                            and std_logic_vector(to_unsigned(j, log2(CHANNELS))) = PCIE_MFB_META(META_CHAN_NUM)
                            ) then

                            if (channel_active_pst(j) = CHANNEL_RUNNING) then
                                pkt_acc_nst(j) <= S_PKT_PENDING;
                                tr_byte_lng_curr(j) <= resize(unsigned(PCIE_MFB_META(META_BYTE_CNT)), log2(PKT_SIZE_MAX+1));
                            else
                                pkt_acc_nst(j)      <= S_PKT_DROP;
                                chan_pkt_drop_en(j) <= (others => '1');
                            end if;
                        end if;

                    when S_PKT_PENDING =>
                        if (PCIE_MFB_SRC_RDY = '1'
                            and PCIE_MFB_SOF = "1"
                            and std_logic_vector(to_unsigned(j, log2(CHANNELS))) = PCIE_MFB_META(META_CHAN_NUM)
                            ) then

                            if (PCIE_MFB_META(META_IS_DMA_HDR) = "1") then

                                pkt_acc_nst(j) <= S_IDLE;

                                if (tr_byte_lng_stored(j) = unsigned(PCIE_MFB_DATA(DMA_FRAME_LENGTH))) then
                                    dma_frame_lng_correct(j) <= '1';
                                else
                                    dma_frame_lng_incorrect(j) <= '1';
                                end if;

                            elsif (PCIE_MFB_META(META_IS_DMA_HDR) = "0") then
                                tr_byte_lng_curr(j) <= tr_byte_lng_stored(j) + resize(unsigned(PCIE_MFB_META(META_BYTE_CNT)), log2(PKT_SIZE_MAX+1));
                            end if;
                        end if;

                    when S_PKT_DROP =>
                        if (PCIE_MFB_SRC_RDY = '1'
                            and PCIE_MFB_SOF = "1"
                            and std_logic_vector(to_unsigned(j, log2(CHANNELS))) = PCIE_MFB_META(META_CHAN_NUM)) then
                            chan_pkt_drop_en(j) <= (others => '1');

                            if (PCIE_MFB_META(META_IS_DMA_HDR) = "1") then
                                pkt_acc_nst(j) <= S_IDLE;
                            end if;
                        end if;
                end case;
            end process;

            dma_hdr_out_of_order_chan(j) <= '1' when (
                pkt_acc_pst(j) = S_IDLE
                and PCIE_MFB_SRC_RDY = '1'
                and PCIE_MFB_DST_RDY = '1'
                and PCIE_MFB_SOF = "1"
                and PCIE_MFB_META(META_IS_DMA_HDR) = "1"
                and std_logic_vector(to_unsigned(j, log2(CHANNELS))) = PCIE_MFB_META(META_CHAN_NUM)
                ) else '0';

        end generate;

    -- Two regions
    else generate
        acceptor_fsm_g : for j in (CHANNELS -1) downto 0 generate
            pkt_acceptor_state_reg_p : process (CLK) is
            begin
                if (rising_edge(CLK)) then
                    if (RESET = '1') then
                        pkt_acc_pst(j) <= S_IDLE;
                    else
                        pkt_acc_pst(j) <= pkt_acc_nst(j);
                    end if;
                end if;
            end process;

            pkt_acceptor_nst_logic_p : process (all) is
            begin
                pkt_acc_nst(j)      <= pkt_acc_pst(j);
                chan_pkt_drop_en(j) <= (others => '0');

                case pkt_acc_pst(j) is
                    -- This process is looking for SOF so that it can move to another state
                    -- The state it moves to is based on channel activity
                    when S_IDLE =>
                        if ((PCIE_MFB_SRC_RDY = '1') and ((or pcie_mfb_sof_arr(j)) = '1')) then

                            -- 2) 4) 6)
                            if (channel_active_pst(j) = CHANNEL_RUNNING) then
                                pkt_acc_nst(j)      <= S_PKT_PENDING;
                            else
                                pkt_acc_nst(j)      <= S_PKT_DROP;
                                chan_pkt_drop_en(j) <= "11";
                            end if;

                            -- 7)
                            -- One transaction in on MFB word
                            -- Possible discard is handled in previous condition
                            -- Very specific - This assumes that SOF was present in first region aswell
                            --               - In no other case does the DMA header appear.
                            if (is_dma_hdr_arr(j)(1) = '1') then
                                pkt_acc_nst(j)      <= S_IDLE;
                            end if;
                        end if;

                    -- This process is looking for DMA header so it can move to S_IDLE
                    -- But there's a catch - There could be combination 8)
                    -- Then we move to S_PKT_PENDING or S_PKT_DROP based on channel activity
                    when S_PKT_PENDING  =>
                        if ((PCIE_MFB_SRC_RDY = '1') and ((or pcie_mfb_sof_arr(j)) = '1')) then

                            -- 8)
                            -- DMA header is in the first region - we must check if there's start of new transaction
                            if (is_dma_hdr_arr(j)(0) = '1') then
                                if (pcie_mfb_sof_arr(j)(1) = '1') then
                                    if (channel_active_pst(j) = CHANNEL_RUNNING) then
                                        pkt_acc_nst(j)          <= S_PKT_PENDING;
                                    else
                                        pkt_acc_nst(j)          <= S_PKT_DROP;
                                        chan_pkt_drop_en(j)(1)  <= '1';
                                    end if;
                                else
                                    -- 5)
                                    pkt_acc_nst(j)      <= S_IDLE;
                                end if;
                            end if;

                            -- 3) 7) 9)
                            -- DMA header is in the second region - always move to S_IDLE
                            if (is_dma_hdr_arr(j)(1) = '1') then
                                pkt_acc_nst(j)      <= S_IDLE;
                            end if;
                        end if;

                    -- This process is looking for DMA header so it can move to S_IDLE
                    -- But there's a catch - There could be combination 8)
                    -- Then we move to S_PKT_PENDING or S_PKT_DROP based on channel activity
                    when S_PKT_DROP =>
                        chan_pkt_drop_en(j) <= "11";
                        if (PCIE_MFB_SRC_RDY = '1') then


                            if ((or pcie_mfb_sof_arr(j)) = '1') then

                                -- 8)
                                -- DMA header is in the first region - we must check if there's start of new transaction
                                if (is_dma_hdr_arr(j)(0) = '1') then
                                    if (pcie_mfb_sof_arr(j)(1) = '1') then
                                        if (channel_active_pst(j) = CHANNEL_RUNNING) then
                                            pkt_acc_nst(j)          <= S_PKT_PENDING;
                                            chan_pkt_drop_en(j)(1)  <= '0';
                                        else
                                            pkt_acc_nst(j)          <= S_PKT_DROP;
                                        end if;
                                    else
                                        -- 5)
                                        pkt_acc_nst(j)      <= S_IDLE;
                                    end if;
                                end if;

                                -- 3) 7) 9)
                                -- DMA header is in the second region - always move to S_IDLE
                                if (is_dma_hdr_arr(j)(1) = '1') then
                                    pkt_acc_nst(j)      <= S_IDLE;
                                end if;
                            end if;
                        end if;
                end case;
            end process;
        end generate;
    end generate;

    -- One region debug (The "PCIE_MFB_SOF = "1"" is not that compatible)
    pkt_statistics_g: if PCIE_MFB_REGIONS = 1 generate
        ST_SP_DBG_CHAN    <= PCIE_MFB_META(META_CHAN_NUM);
        ST_SP_DBG_META(0) <= (or dma_hdr_out_of_order_chan);
        ST_SP_DBG_META(1) <= '1' when (PCIE_MFB_SRC_RDY = '1' and PCIE_MFB_DST_RDY = '1' and PCIE_MFB_SOF = "1" and PCIE_MFB_META(META_IS_DMA_HDR) = "1") else '0';
        ST_SP_DBG_META(2) <= (or dma_frame_lng_correct) and PCIE_MFB_DST_RDY;
        ST_SP_DBG_META(3) <= (or dma_frame_lng_incorrect) and PCIE_MFB_DST_RDY;

        PKT_DISC_CHAN  <= PCIE_MFB_META(META_CHAN_NUM);
        -- choose only packet size from the DMA header
        PKT_DISC_BYTES <= PCIE_MFB_DATA(log2(PKT_SIZE_MAX+1) -1 downto 0);
        PKT_DISC_INC   <= '1' when
                        (
                            pkt_acc_pst(to_integer(unsigned(PCIE_MFB_META(META_CHAN_NUM)))) = S_PKT_DROP
                            and PCIE_MFB_META(META_IS_DMA_HDR) = "1"
                            and PCIE_MFB_SRC_RDY = '1'
                            and PCIE_MFB_DST_RDY = '1')
                        else '0';
    else generate
        -- Extract data for statistics
        -- This part should be compatible with one region as well
        pcie_mfb_data_arr   <= slv_array_deser(PCIE_MFB_DATA, PCIE_MFB_REGIONS);
        discard_arr_p: process(all)
        begin
            for i in PCIE_MFB_REGIONS - 1 downto 0 loop
                pcie_mfb_disc_chan_arr(i)   <= pcie_mfb_meta_arr(i)(META_CHAN_NUM);
                pcie_mfb_disc_bytes_arr(i)  <= pcie_mfb_data_arr(i)(log2(PKT_SIZE_MAX+1) -1 downto 0);

                pcie_mfb_disc_inc_arr(i)    <= '0';
                if (pkt_acc_pst(to_integer(unsigned(pcie_mfb_meta_arr(i)(META_CHAN_NUM)))) = S_PKT_DROP
                    and pcie_mfb_meta_arr(i)(META_IS_DMA_HDR)(0) = '1'
                    and PCIE_MFB_SRC_RDY = '1'
                    and PCIE_MFB_DST_RDY = '1') then
                    pcie_mfb_disc_inc_arr(i)   <= '1';
                end if;
            end loop;
        end process;

        -- Concatenate statistical data
        var_conc_p: process(all)
        begin
            for i in PCIE_MFB_REGIONS - 1 downto 0 loop
                fifox_mult_di(i) <= pcie_mfb_disc_chan_arr(i) & pcie_mfb_disc_bytes_arr(i) & pcie_mfb_disc_inc_arr(i);
            end loop;
        end process;

        -- FIFOX MULTI: (2 to 1) or (1 to 1)
        overflow_fifox_i: entity work.FIFOX_MULTI
        generic map(
            DATA_WIDTH      => log2(CHANNELS) + log2(PKT_SIZE_MAX+1) + 1,
            ITEMS           => CHANNELS*2,
            WRITE_PORTS     => PCIE_MFB_REGIONS,
            READ_PORTS      => 1,
            DEVICE          => DEVICE
        )
        port map (
            CLK     => CLK,
            RESET   => RESET,

            DI      => slv_array_ser(fifox_mult_di),
            WR      => pcie_mfb_disc_inc_arr,
            FULL    => fifox_mult_full,
            AFULL   => open,

            DO      => fifox_mult_do,
            RD      => "1",
            EMPTY   => fifox_mult_empty,
            AEMPTY  => open);

        disc_out_p: process(all)
        begin
            if fifox_mult_empty = "0" then
                (PKT_DISC_CHAN, PKT_DISC_BYTES, PKT_DISC_INC) <= fifox_mult_do;
            else
                (PKT_DISC_CHAN, PKT_DISC_BYTES, PKT_DISC_INC) <= fifox_mult_do;
                PKT_DISC_INC    <= '0';
            end if;
        end process;
    end generate;

    -- =============================================================================================
    -- Packet droping
    --
    -- Meeting specific conditions regarding processing of a current packet and channel active
    -- status will cause every packet on the input to be dropped.
    -- =============================================================================================
    pkt_drop_en_g: for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        pkt_drop_en(i)  <= chan_pkt_drop_en(to_integer(unsigned(pcie_mfb_meta_arr(i)(META_CHAN_NUM))))(i);
    end generate;

    pcie_mfb_meta_ext_g : for i in PCIE_MFB_REGIONS - 1 downto 0 generate
        pcie_mfb_meta_ext(i)(META_IS_DMA_HDR)                                               <= pcie_mfb_meta_arr(i)(META_IS_DMA_HDR) when pkt_drop_en(i) = '0' else (others => '0');
        pcie_mfb_meta_ext(i)(META_CHAN_NUM_O + META_CHAN_NUM_W -1 downto META_IS_DMA_HDR_W) <= pcie_mfb_meta_arr(i)(META_CHAN_NUM_O + META_CHAN_NUM_W -1 downto META_IS_DMA_HDR_W);
        pcie_mfb_meta_ext(i)(META_BE)                                                       <= pcie_mfb_meta_arr(i)(META_BE_O + META_BE_W -1 downto META_BE_O) when pkt_drop_en(i) = '0' else (others => '0');
    end generate;

    pkt_dropper_i : entity work.MFB_DROPPER
        generic map (
            REGIONS     => PCIE_MFB_REGIONS,
            REGION_SIZE => PCIE_MFB_REGION_SIZE,
            BLOCK_SIZE  => PCIE_MFB_BLOCK_SIZE,
            ITEM_WIDTH  => PCIE_MFB_ITEM_WIDTH,
            META_WIDTH  => ((PCIE_MFB_REGION_SIZE*PCIE_MFB_BLOCK_SIZE*PCIE_MFB_ITEM_WIDTH)/8+log2(CHANNELS)+62+1))
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_DATA    => PCIE_MFB_DATA,
            RX_META    => slv_array_ser(pcie_mfb_meta_ext),
            RX_SOF_POS => PCIE_MFB_SOF_POS,
            RX_EOF_POS => PCIE_MFB_EOF_POS,
            RX_SOF     => PCIE_MFB_SOF,
            RX_EOF     => PCIE_MFB_EOF,
            RX_SRC_RDY => PCIE_MFB_SRC_RDY,
            RX_DST_RDY => PCIE_MFB_DST_RDY,
            RX_DROP    => pkt_drop_en,

            TX_DATA    => USR_MFB_DATA,
            TX_META    => USR_MFB_META,
            TX_SOF_POS => USR_MFB_SOF_POS,
            TX_EOF_POS => USR_MFB_EOF_POS,
            TX_SOF     => USR_MFB_SOF,
            TX_EOF     => USR_MFB_EOF,
            TX_SRC_RDY => USR_MFB_SRC_RDY,
            TX_DST_RDY => USR_MFB_DST_RDY);
end architecture;
