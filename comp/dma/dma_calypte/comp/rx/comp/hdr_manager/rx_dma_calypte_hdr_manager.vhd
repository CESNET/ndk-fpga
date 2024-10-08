-- rx_dma_calypte_hdr_manager.vhd: this component generates pcie header and dma headers for the incoming packet
-- Copyright (c) 2024 CESNET z.s.p.o.
-- Author(s): Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;

-- This component generates PCIe headers and DMA header for the incoming packet
-- Fist step is to generate the DMA header. Second is to generate PCIe headers
-- for the packet number of pcie headers is ceil(PKT_SIZE/128) if DMA_DISCARD is
-- not set. Third action is generate pcie header for dma header if DMA_DISCARD
-- is not set. In case when DMA_DISCARD is set then no pcie headers are
-- generated.
entity RX_DMA_CALYPTE_HDR_MANAGER is
    generic (
        MFB_REGIONS : natural := 1;

        -- Number of channels
        CHANNELS      : integer := 16;
        -- Maximum packet size in bytes
        PKT_MTU       : integer := 2**12;
        -- Size of the metadata in the DMA header
        METADATA_SIZE : integer := 24;
        -- RAM address width
        ADDR_WIDTH    : integer := 64;
        -- width of a pointer to the ring buffer log2(NUMBER_OF_ITEMS)
        POINTER_WIDTH : integer := 16;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        --
        -- - "STRATIX10"
        -- - "AGILEX"
        -- - "ULTRASCALE"
        DEVICE        : string  := "ULTRASCALE"
        );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =====================================================================
        -- CHANNEL START/STOP REQUEST INTERFACE
        -- =====================================================================
        -- Index of channel for which a start is requested
        START_REQ_CHANNEL : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        START_REQ_VLD     : in  std_logic;
        -- Channel start confirmation
        START_REQ_DONE    : out std_logic;

        -- Index of channel for whic a stop is requested
        STOP_REQ_CHANNEL : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        STOP_REQ_VLD     : in  std_logic;
        -- Channel stop confirmation
        STOP_REQ_DONE    : out std_logic;

        -- =====================================================================
        -- ADDRESS/POINTER READ INTERFACES
        -- =====================================================================
        -- Request interface for data space
        ADDR_DATA_CHANNEL    : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        ADDR_DATA_BASE       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        ADDR_DATA_MASK       : in  std_logic_vector(POINTER_WIDTH-1 downto 0);
        ADDR_DATA_SW_POINTER : in  std_logic_vector(POINTER_WIDTH-1 downto 0);

        -- Request interface for dma headers
        ADDR_HEADER_CHANNEL    : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        ADDR_HEADER_BASE       : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        ADDR_HEADER_MASK       : in  std_logic_vector(POINTER_WIDTH-1 downto 0);
        ADDR_HEADER_SW_POINTER : in  std_logic_vector(POINTER_WIDTH-1 downto 0);

        -- =====================================================================
        -- HW POINTER UPDATE INTERFACE
        -- =====================================================================
        -- Update data pointers
        HDP_UPDATE_CHAN : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        HDP_UPDATE_DATA : out std_logic_vector(POINTER_WIDTH-1 downto 0);
        HDP_UPDATE_EN   : out std_logic;

        -- Update header pointers
        HHP_UPDATE_CHAN : out std_logic_vector(log2(CHANNELS)-1 downto 0);
        HHP_UPDATE_DATA : out std_logic_vector(POINTER_WIDTH-1 downto 0);
        HHP_UPDATE_EN   : out std_logic;

        -- =====================================================================
        -- INFORMATION ABOUT PACKET (MVB INPUT)
        -- =====================================================================
        -- Input metadata to packet
        INF_META    : in  std_logic_vector(METADATA_SIZE-1 downto 0);
        INF_CHANNEL : in  std_logic_vector(log2(CHANNELS)-1 downto 0);
        INF_SRC_RDY : in  std_logic;
        INF_DST_RDY : out std_logic;

        -- =========================================================================================
        -- Input from data stream
        -- =========================================================================================
        -- Lenght of a currently transported packet in bytes
        STAT_PKT_LNG : in std_logic_vector(log2(PKT_MTU+1) -1 downto 0);
        -- Part of the MFB signals
        MFB_EOF      : in std_logic_vector(MFB_REGIONS -1 downto 0);
        MFB_SRC_RDY  : in std_logic;
        MFB_DST_RDY  : in std_logic;

        -- =====================================================================
        -- PCIE HEADERs (MVB OUTPUT)
        -- =====================================================================
        -- PCIE header size, the values can be (also applies for DATA_PCIE_HDR_SIZE):
        --
        -- * 0 => DMA_PCIE_HDR(3*32-1 downto 0) bits are valid,
        -- * 1 => DMA_PCIE_HDR(4*32-1 downto 0) bits are valid
        DMA_PCIE_HDR_SIZE    : out std_logic;
        DMA_PCIE_HDR         : out std_logic_vector(128-1 downto 0);
        DMA_PCIE_HDR_SRC_RDY : out std_logic;
        DMA_PCIE_HDR_DST_RDY : in  std_logic;

        DATA_PCIE_HDR_SIZE    : out std_logic;
        DATA_PCIE_HDR         : out std_logic_vector(128-1 downto 0);
        DATA_PCIE_HDR_SRC_RDY : out std_logic;
        DATA_PCIE_HDR_DST_RDY : in  std_logic;

        -- =====================================================================
        -- PCIE HEADER (MVB OUTPUT)
        -- =====================================================================
        -- Signals if the current packet should be discarded
        DMA_DISCARD     : out std_logic;
        -- DMA header content
        DMA_HDR         : out std_logic_vector(64-1 downto 0);
        DMA_HDR_SRC_RDY : out std_logic;
        DMA_HDR_DST_RDY : in  std_logic;

        -- =========================================================================================
        -- Pkt counter interface
        -- =========================================================================================
        PKT_CNTR_CHAN     : out std_logic_vector(log2(CHANNELS) -1 downto 0);
        PKT_CNTR_SENT_INC : out std_logic;
        PKT_CNTR_DISC_INC : out std_logic;
        PKT_CNTR_PKT_SIZE : out std_logic_vector(log2(PKT_MTU+1) -1 downto 0)
        );
end entity;

architecture FULL of RX_DMA_CALYPTE_HDR_MANAGER is

    -- Byte length of a segment, e.g. the length of a PCIe transaction with data
    constant DATA_SEGMENT_SIZE : natural := 128;
    -- Subrange of packet length that determines how much segments a packet consists from
    subtype BLK_CNT is natural range log2(PKT_MTU+1)-1 downto log2(DATA_SEGMENT_SIZE);

    -- =============================================================================================
    -- Start/stop logic
    -- =============================================================================================
    -- Status register. This register represents if channel is running or it is stopped.
    signal channel_status_reg : std_logic_vector(CHANNELS-1 downto 0);
    signal channel_status_new : std_logic_vector(CHANNELS-1 downto 0);

    type chan_state_change_t is (S_IDLE, S_WAIT_FOR_PKT_END);
    signal chan_state_change_pst : chan_state_change_t := S_IDLE;
    signal chan_state_change_nst : chan_state_change_t := S_IDLE;

    -- Store register for the information if the start request is currently pending (set to 0 if a
    -- stop request is currently pending). This is only used when there is a packet currently
    -- processed in the pipeline that either passes (in case of a stop request) or is dropped (in
    -- case of a start request).
    signal is_start_req_pending_reg : std_logic;
    signal is_start_req_pending_new : std_logic;
    -- Output register of *_REQ_DONE signals
    signal start_req_done_int       : std_logic;
    signal stop_req_done_int        : std_logic;

    -- =============================================================================================
    -- Input FIFO
    -- =============================================================================================
    -- Width of data in the input FIFO
    constant INP_FIFO_W    : natural := METADATA_SIZE + log2(CHANNELS);
    constant INP_FIFO_SIZE : natural := 8;

    -- Signals of the input FIFO
    signal input_fifo_in    : std_logic_vector(INP_FIFO_W -1 downto 0);
    signal input_fifo_wr    : std_logic;
    signal input_fifo_full  : std_logic;
    signal input_fifo_do    : std_logic_vector(INP_FIFO_W -1 downto 0);
    signal input_fifo_rd    : std_logic;
    signal input_fifo_empty : std_logic;

    -- This signals from input_fifo_do
    signal input_meta    : std_logic_vector(METADATA_SIZE -1 downto 0);
    signal input_channel : std_logic_vector(log2(CHANNELS) -1 downto 0);

    -- =============================================================================================
    -- PCIe header FIFOs
    -- =============================================================================================
    -- Width of data in the FIFO for PCIe headers of transactions carrying DMA header
    constant PCIE_HDR_DMA_TRAN_FIFO_W     : natural := 1 + 128;
    constant PCIE_HDR_DMA_TRAN_FIFO_SIZE  : natural := 8;
    -- Width of data in the FIFO for PCIe headers of transactions carrying user data
    constant PCIE_HDR_DATA_TRAN_FIFO_W    : natural := 1 + 128;
    constant PCIE_HDR_DATA_TRAN_FIFO_SIZE : natural := 8;

    -- Signals for the FIFO that carries the PCIe headers for transactions with DMA headers
    signal pcie_hdr_dma_hdr_tran_fifo_in    : std_logic_vector(PCIE_HDR_DMA_TRAN_FIFO_W -1 downto 0);
    signal pcie_hdr_dma_hdr_tran_fifo_wr    : std_logic;
    signal pcie_hdr_dma_hdr_tran_fifo_full  : std_logic;
    signal pcie_hdr_dma_hdr_tran_fifo_do    : std_logic_vector (PCIE_HDR_DMA_TRAN_FIFO_W -1 downto 0);
    signal pcie_hdr_dma_hdr_tran_fifo_rd    : std_logic;
    signal pcie_hdr_dma_hdr_tran_fifo_empty : std_logic;

    -- Signals for the FIFO tha carries the PCIe headers for transactions with user data
    signal pcie_hdr_data_tran_fifo_in    : std_logic_vector(PCIE_HDR_DATA_TRAN_FIFO_W -1 downto 0);
    signal pcie_hdr_data_tran_fifo_wr    : std_logic;
    signal pcie_hdr_data_tran_fifo_full  : std_logic;
    signal pcie_hdr_data_tran_fifo_do    : std_logic_vector(PCIE_HDR_DATA_TRAN_FIFO_W -1 downto 0);
    signal pcie_hdr_data_tran_fifo_rd    : std_logic;
    signal pcie_hdr_data_tran_fifo_empty : std_logic;

    -- =============================================================================================
    -- Data transaction PCIe header generator
    -- =============================================================================================
    -- Address for a data PCIe transaction
    signal data_pcie_addr          : std_logic_vector(ADDR_WIDTH -1 downto 0);
    signal data_pcie_addr_reg      : std_logic_vector(ADDR_WIDTH -1 downto 0);
    -- Data pointer of a current segment
    signal data_ptr                : std_logic_vector(POINTER_WIDTH -1 downto 0);
    signal data_pcie_addr_vld      : std_logic;
    -- determines if the PCIe header is the size of 3 or 4 DWs
    signal pcie_addr_len_data_tran : std_logic;
    -- Content of a PCIE header for a transaction with user data
    signal pcie_hdr_data_tran      : std_logic_vector(128-1 downto 0);

    -- =============================================================================================
    -- DMA header PCIe header generator
    -- =============================================================================================
    -- Address for a DMA header PCIe transaction
    signal dma_hdr_pcie_addr          : std_logic_vector(ADDR_WIDTH -1 downto 0);
    signal dma_hdr_pcie_addr_reg      : std_logic_vector(ADDR_WIDTH -1 downto 0);
    signal dma_hdr_pcie_addr_vld      : std_logic;
    -- determines if the PCIe header is the size of 3 or 4 DWs
    signal pcie_addr_len_dma_hdr_tran : std_logic;
    -- Content of a PCIe header for a transaction with DMA header
    signal pcie_hdr_dma_hdr_tran      : std_logic_vector(128-1 downto 0);

    -- =============================================================================================
    -- FSM that tracks the current state of the packet reception
    -- =============================================================================================
    type packet_process_fsm_t is (S_IDLE, S_PACKET_PROCESS, S_PACKET_DISCARD);
    signal pkt_process_pst : packet_process_fsm_t := S_IDLE;
    signal pkt_process_nst : packet_process_fsm_t := S_IDLE;

    constant DATA_ADDR_NEXT_FIFO_W    : positive := 1 + log2(CHANNELS);
    constant DATA_ADDR_NEXT_FIFO_SIZE : positive := 8;
    -- Asserts if the request of either a next address for a data transaction or a DMA header
    -- transaction is issued
    signal data_addr_chan             : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal data_addr_next             : std_logic;
    signal data_addr_next_n           : std_logic;
    signal data_addr_next_wr          : std_logic;
    signal data_addr_next_fifo_do     : std_logic_vector(DATA_ADDR_NEXT_FIFO_W -1 downto 0);

    constant DMA_HDR_ADDR_NEXT_FIFO_W    : positive := log2(CHANNELS);
    constant DMA_HDR_ADDR_NEXT_FIFO_SIZE : positive := 8;
    signal dma_hdr_addr_chan             : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal dma_hdr_addr_next             : std_logic;
    signal dma_hdr_addr_next_n           : std_logic;
    signal dma_hdr_addr_next_wr          : std_logic;

    signal pkt_chan_reg : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal pkt_chan_new : std_logic_vector(log2(CHANNELS) -1 downto 0);
    -- Storing the length of a portion of packet that was already accepted in order to correctly
    -- generate PCIe headers for its segments
    signal pkt_lng_reg  : std_logic_vector(log2((PKT_MTU/DATA_SEGMENT_SIZE)+1) -1 downto 0);
    signal pkt_lng_new  : std_logic_vector(log2((PKT_MTU/DATA_SEGMENT_SIZE)+1) -1 downto 0);

    signal pkt_discard_vld   : std_logic;
    -- A flag in the data_addr_next_fifo_i that tells that the data pointer neds to be stored with
    -- the valid address in order to be correctly assigned to the DMA header.
    signal store_data_ptr_wr : std_logic;
    signal store_data_ptr    : std_logic;

    -- Increments for packet counters
    signal pkt_cntr_sent_inc_int : std_logic;
    signal pkt_cntr_disc_inc_int : std_logic;

    -- =============================================================================================
    -- FIFOs for DMA header and its metadata
    --
    -- Those FIFOs are here so they can keep the information about the transmitted packets even when
    -- the parallel packet processing pipeline has already advanced (there are more packets stored
    -- in the pipeline). That is because the valid address does not have to come expectedly in the
    -- next clock cycle and, therefore, the requests for the address need to be kept in the FIFO.
    -- =============================================================================================
    -- The FIFOs containing DMA header parts all contain the same size
    constant DMA_HDR_FIFO_SIZE : natural := 8;

    signal discard_fifo_wr    : std_logic;
    signal discard_fifo_do    : std_logic_vector(0 downto 0);
    signal discard_fifo_rd    : std_logic;
    signal discard_fifo_empty : std_logic;

    signal pkt_size_fifo_wr    : std_logic;
    signal pkt_size_fifo_do    : std_logic_vector(log2(PKT_MTU+1) -1 downto 0);
    signal pkt_size_fifo_rd    : std_logic;
    signal pkt_size_fifo_empty : std_logic;

    signal hdr_meta_fifo_wr    : std_logic;
    signal hdr_meta_fifo_do    : std_logic_vector(METADATA_SIZE -1 downto 0);
    signal hdr_meta_fifo_rd    : std_logic;
    signal hdr_meta_fifo_empty : std_logic;

    signal ptr_fifo_do    : std_logic_vector(POINTER_WIDTH -1 downto 0);
    signal ptr_fifo_rd    : std_logic;
    signal ptr_fifo_empty : std_logic;

    -- =============================================================================================
    -- Debug signals and probes (either for verification or ILA/SignalTap)
    -- =============================================================================================
    -- Counts the overall amount of reads from the input FIFO and the writes to the DMA FIFO. These
    -- counters must be equal on the end of a verification.
    signal inp_fifo_rd_cntr     : unsigned(64 downto 0);
    signal dma_hdr_fifo_rd_cntr : unsigned(64 downto 0);

    -- Observing the fullness of the FIFOs. Their size is set to such a value in which they should
    -- not overflow even in case of the constant packet transmission. This signals are put into
    -- assertions in order to check this.
    signal discard_fifo_full           : std_logic;
    signal pkt_size_fifo_full          : std_logic;
    signal hdr_meta_fifo_full          : std_logic;
    signal ptr_fifo_full               : std_logic;
    signal data_addr_next_fifo_full    : std_logic;
    signal dma_hdr_addr_next_fifo_full : std_logic;

    -- attribute mark_debug : string;
begin

    -- =============================================================================================
    -- Assertions for verification
    -- =============================================================================================
    pcie_hdr_fifo_full_check_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '0') then
                assert (pcie_hdr_dma_hdr_tran_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the PCIe header transaction FIFO occured!"
                    severity FAILURE;
                assert (pcie_hdr_data_tran_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the PCIe data transaction FIFO occured!"
                    severity FAILURE;
                assert (data_addr_next_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the FIFO for data address requests occured!"
                    severity FAILURE;
                assert (dma_hdr_addr_next_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the FIFO for DMA header address requests occured!"
                    severity FAILURE;
                assert (discard_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the Discard FIFO occured!"
                    severity FAILURE;
                assert (pkt_size_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the Packet Size FIFO occured!"
                    severity FAILURE;
                assert (hdr_meta_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the Header Meta FIFO occured!"
                    severity FAILURE;
                assert (ptr_fifo_full = '0')
                    report "RX_DMA_HDR_MANAGER: Complete filling of the Pointer FIFO occured!"
                    severity FAILURE;
            end if;
        end if;
    end process;

    -- =============================================================================================
    -- Debug signals for verification
    -- =============================================================================================
    inp_fifo_wr_cntr_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dma_hdr_fifo_rd_cntr <= (others => '0');
                inp_fifo_rd_cntr     <= (others => '0');
            else
                if (input_fifo_rd = '1' and input_fifo_empty = '0') then
                    inp_fifo_rd_cntr <= inp_fifo_rd_cntr + 1;
                end if;

                if (DMA_HDR_SRC_RDY = '1' and DMA_HDR_DST_RDY = '1') then
                    dma_hdr_fifo_rd_cntr <= dma_hdr_fifo_rd_cntr + 1;
                end if;
            end if;
        end if;
    end process;

    --=====================================================================
    -- INPUT FIFO
    --=====================================================================
    input_fifo_in <= INF_META & INF_CHANNEL;
    -- the write is permitted only if there are a valid data on the input and the FIFO is not full
    input_fifo_wr <= INF_SRC_RDY;
    INF_DST_RDY   <= not input_fifo_full;

    input_mvb_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => INP_FIFO_W,
            ITEMS               => INP_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI   => input_fifo_in,
            WR   => input_fifo_wr,
            FULL => input_fifo_full,

            DO    => input_fifo_do,
            RD    => input_fifo_rd,
            EMPTY => input_fifo_empty);

    (input_meta, input_channel) <= input_fifo_do;

    --=====================================================================
    -- Channel activity FSM
    --=====================================================================
    -- This state machine controls the start/stop process on a channel. An inactive channel is
    -- dropping packets. If a start request is being issued on a channel, a currently dropped packet
    -- needs to be dropped entirely and the channel is then activated. If the channel did not drop
    -- any packets upon the start request, it is simply activated and prepared for incoming packets.
    -- An active channel processes its packets, meaning each packet is send to the host memory.
    --
    -- If stop request is being issued on a channel, the channel needs to finish processing its
    -- current packet and then it is inactive. If no packet has been processed upon the stop
    -- request, the channel is simply disactivated.

    channel_status_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                chan_state_change_pst    <= S_IDLE;
                channel_status_reg       <= (others => '0');
                is_start_req_pending_reg <= '0';
            else
                chan_state_change_pst    <= chan_state_change_nst;
                channel_status_reg       <= channel_status_new;
                is_start_req_pending_reg <= is_start_req_pending_new;
            end if;
        end if;
    end process;

    channel_status_p : process (all)
    begin
        chan_state_change_nst    <= chan_state_change_pst;
        channel_status_new       <= channel_status_reg;
        is_start_req_pending_new <= is_start_req_pending_reg;
        start_req_done_int       <= '0';
        stop_req_done_int        <= '0';

        case chan_state_change_pst is
            when S_IDLE =>

                if (STOP_REQ_VLD = '1') then
                    channel_status_new(to_integer(unsigned(STOP_REQ_CHANNEL))) <= '0';

                    -- If the channel the request was sent on does not have a packet processed on
                    -- it, acknowledge the stop immediately and do not wait for anything.
                    if (pkt_chan_reg /= STOP_REQ_CHANNEL or pkt_process_pst /= S_PACKET_PROCESS) then
                        stop_req_done_int <= '1';
                    else
                        -- If the channel to be stopped is processing a packet, do not
                        -- acknowledge the stop of a channel but switch to S_WAIT_FOR_PKT_END state.
                        chan_state_change_nst    <= S_WAIT_FOR_PKT_END;
                        is_start_req_pending_new <= '0';
                    end if;

                elsif (START_REQ_VLD = '1') then
                    channel_status_new(to_integer(unsigned(START_REQ_CHANNEL))) <= '1';

                    -- If the channel the request was sent on does not have a packet dropped on
                    -- it, acknowledge the start immediately and do not wait for anything.
                    if (pkt_chan_reg /= START_REQ_CHANNEL or pkt_process_pst /= S_PACKET_DISCARD) then
                        start_req_done_int <= '1';
                    else
                        -- If the channel to be started is dropping a packet, do not
                        -- acknowledge the stop of a channel but switch to S_WAIT_FOR_PKT_END state.
                        chan_state_change_nst    <= S_WAIT_FOR_PKT_END;
                        -- Store the information if this was a start request to assert a correct
                        -- *_done signal after packet end.
                        is_start_req_pending_new <= '1';
                    end if;
                end if;

            -- Wait for the packet to be processed/dropped.
            when S_WAIT_FOR_PKT_END =>

                if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                    chan_state_change_nst <= S_IDLE;

                    if (is_start_req_pending_reg = '1') then
                        start_req_done_int <= '1';
                    else
                        stop_req_done_int <= '1';
                    end if;
                end if;
        end case;
    end process;

    -- A register to add a 1 clock delay that is expected by the software manager.
    start_stop_req_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            START_REQ_DONE <= start_req_done_int;
            STOP_REQ_DONE  <= stop_req_done_int;
        end if;
    end process;

    -- =============================================================================================
    -- FSM for packet processing
    -- =============================================================================================
    -- This FSM observes the current state of packet transmission and drives the FIFOs that put
    -- requests on PCIe header generation as well as a generation of a DMA header.
    pkt_process_fsm_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pkt_process_pst <= S_IDLE;
                pkt_chan_reg    <= (others => '0');
                pkt_lng_reg     <= (others => '0');
            else
                pkt_process_pst <= pkt_process_nst;
                pkt_chan_reg    <= pkt_chan_new;
                pkt_lng_reg     <= pkt_lng_new;
            end if;
        end if;
    end process;

    pkt_process_nst_logic_p : process (all) is
    begin
        pkt_process_nst <= pkt_process_pst;

        case pkt_process_pst is
            when S_IDLE =>

                if (input_fifo_empty = '0') then
                    if (channel_status_reg(to_integer(unsigned(input_channel))) = '1') then
                        -- if there is a one-word packet, then do not transition
                        if (not (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1')) then
                            pkt_process_nst <= S_PACKET_PROCESS;
                        end if;
                    else
                        if (not (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1')) then
                            pkt_process_nst <= S_PACKET_DISCARD;
                        end if;
                    end if;
                end if;

            when S_PACKET_PROCESS =>

                if (MFB_SRC_RDY = '1' and MFB_DST_RDY = '1' and MFB_EOF = "1") then
                    pkt_process_nst <= S_IDLE;
                end if;

            when S_PACKET_DISCARD =>

                if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                    pkt_process_nst <= S_IDLE;
                end if;
        end case;
    end process;

    pkt_process_output_logic_p : process (all) is
    begin
        pkt_chan_new <= pkt_chan_reg;
        pkt_lng_new  <= pkt_lng_reg;

        input_fifo_rd <= '0';

        data_addr_next_wr    <= '0';
        dma_hdr_addr_next_wr <= '0';

        store_data_ptr_wr <= '0';

        pkt_discard_vld  <= '0';
        discard_fifo_wr  <= '0';
        pkt_size_fifo_wr <= '0';
        hdr_meta_fifo_wr <= '0';

        pkt_cntr_sent_inc_int <= '0';
        pkt_cntr_disc_inc_int <= '0';

        case pkt_process_pst is
            when S_IDLE =>

                if (input_fifo_empty = '0') then
                    pkt_chan_new <= input_channel;
                    pkt_lng_new  <= (others => '0');

                    if (channel_status_reg(to_integer(unsigned(input_channel))) = '1') then
                        -- There is a small packet that fits to one bus word
                        if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                            input_fifo_rd         <= '1';
                            pkt_size_fifo_wr      <= '1';
                            pkt_cntr_sent_inc_int <= '1';
                        end if;

                        -- Put requests for next address to both FIFOs
                        data_addr_next_wr    <= '1';
                        dma_hdr_addr_next_wr <= '1';
                        store_data_ptr_wr    <= '1';

                        -- THe discard information (set to 0) and the DMA header metadata can be put to the
                        -- output FIFOs immediately.
                        discard_fifo_wr  <= '1';
                        hdr_meta_fifo_wr <= '1';
                    else
                        -- There is a small packet that fits to one bus word
                        if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                            input_fifo_rd         <= '1';
                            pkt_cntr_disc_inc_int <= '1';
                        end if;

                        -- Only the discard information is put to its output FIFO
                        pkt_discard_vld <= '1';
                        discard_fifo_wr <= '1';
                    end if;
                end if;

            when S_PACKET_PROCESS =>

                if (MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                    -- Another block of data has been received, update the data pointer and generate new
                    -- PCIe header
                    if (STAT_PKT_LNG(BLK_CNT) > pkt_lng_reg and MFB_EOF = "0") then
                        pkt_lng_new       <= STAT_PKT_LNG(BLK_CNT);
                        data_addr_next_wr <= '1';
                    end if;

                    -- TODO: Also switch to idle when the length of a current packet overflows.
                    if (MFB_EOF = "1") then
                        input_fifo_rd         <= '1';
                        pkt_size_fifo_wr      <= '1';
                        pkt_cntr_sent_inc_int <= '1';
                    end if;
                end if;

            when S_PACKET_DISCARD =>

                if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                    input_fifo_rd         <= '1';
                    pkt_cntr_disc_inc_int <= '1';
                end if;
        end case;
    end process;

    -- A register for counter increment signals since the channel number can change
    -- with the next packet.
    frame_lng_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            PKT_CNTR_SENT_INC <= pkt_cntr_sent_inc_int;
            PKT_CNTR_DISC_INC <= pkt_cntr_disc_inc_int;

            if (MFB_EOF = "1" and MFB_SRC_RDY = '1' and MFB_DST_RDY = '1') then
                PKT_CNTR_CHAN     <= input_channel;
                PKT_CNTR_PKT_SIZE <= STAT_PKT_LNG;
            end if;
        end if;
    end process;

    data_addr_next_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => DATA_ADDR_NEXT_FIFO_W,
            ITEMS               => DATA_ADDR_NEXT_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => store_data_ptr_wr & input_channel,
            WR     => data_addr_next_wr,
            FULL   => data_addr_next_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => data_addr_next_fifo_do,
            RD     => data_pcie_addr_vld,
            EMPTY  => data_addr_next_n,
            AEMPTY => open);

    (store_data_ptr, data_addr_chan) <= data_addr_next_fifo_do;

    dma_hdr_addr_next_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => DMA_HDR_ADDR_NEXT_FIFO_W,
            ITEMS               => DMA_HDR_ADDR_NEXT_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => input_channel,
            WR     => dma_hdr_addr_next_wr,
            FULL   => dma_hdr_addr_next_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => dma_hdr_addr_chan,
            RD     => dma_hdr_pcie_addr_vld,
            EMPTY  => dma_hdr_addr_next_n,
            AEMPTY => open);

    data_addr_next    <= (not data_addr_next_n) and (not data_pcie_addr_vld);
    dma_hdr_addr_next <= (not dma_hdr_addr_next_n) and (not dma_hdr_pcie_addr_vld);

    -- =============================================================================================
    -- PCIe header generation
    -- =============================================================================================
    data_pcie_addr_mgr_i : entity work.RX_DMA_CALYPTE_ADDR_MANAGER
        generic map (
            CHANNELS      => CHANNELS,
            BLOCK_SIZE    => DATA_SEGMENT_SIZE,
            ADDR_WIDTH    => ADDR_WIDTH,
            POINTER_WIDTH => POINTER_WIDTH,
            DEVICE        => DEVICE)
        port map (
            CLK   => CLK,
            RESET => RESET,

            ADDR_CHANNEL    => ADDR_DATA_CHANNEL,
            ADDR_BASE       => ADDR_DATA_BASE,
            ADDR_MASK       => ADDR_DATA_MASK,
            ADDR_SW_POINTER => ADDR_DATA_SW_POINTER,

            POINTER_UPDATE_CHAN => HDP_UPDATE_CHAN,
            POINTER_UPDATE_DATA => HDP_UPDATE_DATA,
            POINTER_UPDATE_EN   => HDP_UPDATE_EN,

            CHANNEL     => data_addr_chan,
            CHANNEL_VLD => data_addr_next,

            START_REQ_VLD     => START_REQ_VLD,
            START_REQ_CHANNEL => START_REQ_CHANNEL,

            ADDR     => data_pcie_addr,
            OFFSET   => data_ptr,
            ADDR_VLD => data_pcie_addr_vld);

    pcie_hdr_gen_data_i : entity work.PCIE_RQ_HDR_GEN
        generic map (
            DEVICE => DEVICE)
        port map (
            IN_ADDRESS    => data_pcie_addr_reg(63 downto 2),
            IN_VFID       => (others => '0'),
            IN_TAG        => (others => '0'),
            IN_DW_CNT     => std_logic_vector(to_unsigned(DATA_SEGMENT_SIZE/4, 11)),
            IN_ATTRIBUTES => "000",
            IN_FBE        => "1111",
            IN_LBE        => "1111",
            IN_ADDR_LEN   => pcie_addr_len_data_tran,
            IN_REQ_TYPE   => '1',       -- only memory writes

            OUT_HEADER => pcie_hdr_data_tran);

    dma_hdr_pcie_addr_mgr_i : entity work.RX_DMA_CALYPTE_ADDR_MANAGER
        generic map (
            CHANNELS      => CHANNELS,
            BLOCK_SIZE    => 8,
            ADDR_WIDTH    => ADDR_WIDTH,
            POINTER_WIDTH => POINTER_WIDTH,
            DEVICE        => DEVICE)
        port map (
            CLK   => CLK,
            RESET => RESET,

            ADDR_CHANNEL    => ADDR_HEADER_CHANNEL,
            ADDR_BASE       => ADDR_HEADER_BASE,
            ADDR_MASK       => ADDR_HEADER_MASK,
            ADDR_SW_POINTER => ADDR_HEADER_SW_POINTER,

            POINTER_UPDATE_CHAN => HHP_UPDATE_CHAN,
            POINTER_UPDATE_DATA => HHP_UPDATE_DATA,
            POINTER_UPDATE_EN   => HHP_UPDATE_EN,

            CHANNEL     => dma_hdr_addr_chan,
            CHANNEL_VLD => dma_hdr_addr_next,

            START_REQ_VLD     => START_REQ_VLD,
            START_REQ_CHANNEL => START_REQ_CHANNEL,

            ADDR     => dma_hdr_pcie_addr,
            OFFSET   => open,
            ADDR_VLD => dma_hdr_pcie_addr_vld);

    pcie_hdr_gen_dma_i : entity work.PCIE_RQ_HDR_GEN
        generic map (
            DEVICE => DEVICE)
        port map (
            IN_ADDRESS    => dma_hdr_pcie_addr_reg(63 downto 2),
            IN_VFID       => (others => '0'),
            IN_TAG        => (others => '0'),
            IN_DW_CNT     => std_logic_vector(to_unsigned(8/4, 11)),
            IN_ATTRIBUTES => "000",
            IN_FBE        => "1111",
            IN_LBE        => "1111",
            IN_ADDR_LEN   => pcie_addr_len_dma_hdr_tran,
            IN_REQ_TYPE   => '1',       -- only memory writes

            OUT_HEADER => pcie_hdr_dma_hdr_tran);

    -- =============================================================================================
    -- FIFOs for PCIe headers of the data and the DMA header
    -- =============================================================================================
    pcie_hdr_dma_hdr_tran_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            dma_hdr_pcie_addr_reg         <= dma_hdr_pcie_addr;
            pcie_hdr_dma_hdr_tran_fifo_wr <= dma_hdr_pcie_addr_vld;
            pcie_addr_len_dma_hdr_tran    <= '1' when (DEVICE = "ULTRASCALE" or dma_hdr_pcie_addr(64-1 downto 32) /= (32-1 downto 0 => '0')) else '0';
        end if;
    end process;

    pcie_hdr_dma_hdr_tran_fifo_in <= pcie_addr_len_dma_hdr_tran & pcie_hdr_dma_hdr_tran;

    pcie_hdr_dma_hdr_tran_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => PCIE_HDR_DMA_TRAN_FIFO_W,
            ITEMS               => PCIE_HDR_DMA_TRAN_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => pcie_hdr_dma_hdr_tran_fifo_in,
            WR     => pcie_hdr_dma_hdr_tran_fifo_wr,
            FULL   => pcie_hdr_dma_hdr_tran_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => pcie_hdr_dma_hdr_tran_fifo_do,
            RD     => pcie_hdr_dma_hdr_tran_fifo_rd,
            EMPTY  => pcie_hdr_dma_hdr_tran_fifo_empty,
            AEMPTY => open);

    (DMA_PCIE_HDR_SIZE, DMA_PCIE_HDR) <= pcie_hdr_dma_hdr_tran_fifo_do;
    DMA_PCIE_HDR_SRC_RDY              <= not pcie_hdr_dma_hdr_tran_fifo_empty;
    pcie_hdr_dma_hdr_tran_fifo_rd     <= DMA_PCIE_HDR_DST_RDY;

    pcie_hdr_data_tran_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            data_pcie_addr_reg <= data_pcie_addr;
            pcie_hdr_data_tran_fifo_wr <= data_pcie_addr_vld;
            pcie_addr_len_data_tran <= '1' when (DEVICE = "ULTRASCALE" or data_pcie_addr(64-1 downto 32) /= (32-1 downto 0 => '0')) else '0';
        end if;
    end process;

    pcie_hdr_data_tran_fifo_in <= pcie_addr_len_data_tran & pcie_hdr_data_tran;

    pcie_hdr_data_tran_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => PCIE_HDR_DATA_TRAN_FIFO_W,
            ITEMS               => PCIE_HDR_DATA_TRAN_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => pcie_hdr_data_tran_fifo_in,
            WR     => pcie_hdr_data_tran_fifo_wr,
            FULL   => pcie_hdr_data_tran_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => pcie_hdr_data_tran_fifo_do,
            RD     => pcie_hdr_data_tran_fifo_rd,
            EMPTY  => pcie_hdr_data_tran_fifo_empty,
            AEMPTY => open);

    (DATA_PCIE_HDR_SIZE, DATA_PCIE_HDR) <= pcie_hdr_data_tran_fifo_do;
    DATA_PCIE_HDR_SRC_RDY               <= not pcie_hdr_data_tran_fifo_empty;
    pcie_hdr_data_tran_fifo_rd          <= DATA_PCIE_HDR_DST_RDY;

    -- =============================================================================================
    -- FIFOs for DMA header parts
    -- =============================================================================================

    dma_discard_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => 1,
            ITEMS               => DMA_HDR_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => (others => pkt_discard_vld),
            WR     => discard_fifo_wr,
            FULL   => discard_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => discard_fifo_do,
            RD     => discard_fifo_rd,
            EMPTY  => discard_fifo_empty,
            AEMPTY => open);

    -- The discard signal is simply read to the output since it is always with generated with every
    -- packet. (The metadata like packet size, DMA metadata and packet pointer are read only if the
    -- discard is set to 0 for the corresponding packet).
    discard_fifo_rd <= DMA_HDR_DST_RDY;

    pkt_size_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => log2(PKT_MTU+1),
            ITEMS               => DMA_HDR_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => STAT_PKT_LNG,
            WR     => pkt_size_fifo_wr,
            FULL   => pkt_size_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => pkt_size_fifo_do,
            RD     => pkt_size_fifo_rd,
            EMPTY  => pkt_size_fifo_empty,
            AEMPTY => open);

    -- Read from the FIFO only if the discard signal is 0 and all other metadata are valid
    pkt_size_fifo_rd <= DMA_HDR_DST_RDY and (not hdr_meta_fifo_empty) and (not ptr_fifo_empty) and (not discard_fifo_empty) and (not discard_fifo_do(0));

    hdr_meta_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => METADATA_SIZE,
            ITEMS               => DMA_HDR_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => input_meta,
            WR     => hdr_meta_fifo_wr,
            FULL   => hdr_meta_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => hdr_meta_fifo_do,
            RD     => hdr_meta_fifo_rd,
            EMPTY  => hdr_meta_fifo_empty,
            AEMPTY => open);

    -- Read from the FIFO only if the discard signal is 0 and all other metadata are valid
    hdr_meta_fifo_rd <= DMA_HDR_DST_RDY and (not pkt_size_fifo_empty) and (not ptr_fifo_empty) and (not discard_fifo_empty) and (not discard_fifo_do(0));

    ptr_fifo_i : entity work.FIFOX
        generic map (
            DATA_WIDTH          => POINTER_WIDTH,
            ITEMS               => DMA_HDR_FIFO_SIZE,
            RAM_TYPE            => "LUT",
            DEVICE              => DEVICE,
            ALMOST_FULL_OFFSET  => 0,
            ALMOST_EMPTY_OFFSET => 0,
            FAKE_FIFO           => FALSE)
        port map(
            CLK   => CLK,
            RESET => RESET,

            DI     => data_ptr,
            WR     => store_data_ptr and data_pcie_addr_vld,
            FULL   => ptr_fifo_full,
            AFULL  => open,
            STATUS => open,

            DO     => ptr_fifo_do,
            RD     => ptr_fifo_rd,
            EMPTY  => ptr_fifo_empty,
            AEMPTY => open);

    -- Read from the FIFO only if the discard signal is 0 and all other metadata are valid
    ptr_fifo_rd <= DMA_HDR_DST_RDY and (not pkt_size_fifo_empty) and (not hdr_meta_fifo_empty) and (not discard_fifo_empty) and (not discard_fifo_do(0));

    -- =============================================================================================
    -- FIFO for DMA Headers
    -- =============================================================================================
    DMA_DISCARD <= discard_fifo_do(0);
    DMA_HDR     <= (24-1 downto METADATA_SIZE => '0')
               & hdr_meta_fifo_do
               & (7-1 downto 0                => '0')
               & '1'
               & std_logic_vector(resize(unsigned(ptr_fifo_do), 16))
               & (16-1 downto log2(PKT_MTU+1) => '0')
               & pkt_size_fifo_do;

    -- A header is valid if either all discard signal is to 0 and all parts are valid OR the discard
    -- signal is valid and set to 1.
    DMA_HDR_SRC_RDY <= ((not hdr_meta_fifo_empty) and (not ptr_fifo_empty) and (not pkt_size_fifo_empty) and (not discard_fifo_empty) and (not discard_fifo_do(0)))
                       or ((not discard_fifo_empty) and discard_fifo_do(0));
end architecture;
