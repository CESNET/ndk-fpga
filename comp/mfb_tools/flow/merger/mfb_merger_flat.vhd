-- mfb_merger_flat.vhd: MFB+MVB bus merger with a flat arbiter
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- MFB+MVB bus merger which arbitrates all its inputs in a single step.
--
-- Merges ``MERGER_INPUTS`` input MVB+MFB streams into one output stream.
--
-- The MVB interface carries headers and the MFB interface the data payload.
-- ``RX_MVB_PAYLOAD(i)(j)='1'`` marks that the j-th header on input i has a
-- frame on MFB. On each input the k-th frame belongs to the k-th header that
-- announces one. Headers and frames must therefore keep the same order.
--
-- **How it works**
--
-- Headers and payload are merged by two separate halves. The MVB half is a
-- plain arbiter built on :vhdl:entity:`MVB_MERGE_STREAMS`. It picks one input
-- and lets its headers out. For every header that announces a payload it also
-- writes the number of that input into the switch FIFO.
--
-- The switch FIFO holds one item per packet, in the order the packets leave.
-- The MFB half reads it to learn which input each output word is built from.
-- Every input holds its current word in a register. The packet counts kept
-- beside that register decide how much of the word may leave at once.
--
entity MFB_MERGER_FLAT is
    generic (
        -- Number of merger input streams, must be at least 2
        MERGER_INPUTS    : natural := 4;

        -- Number of MVB header items (parallel headers per cycle)
        MVB_ITEMS        : natural := 2;
        -- Width of each MVB header item in bits
        MVB_ITEM_WIDTH   : natural := 32;

        -- Number of Regions per MFB word
        MFB_REGIONS      : natural := 2;
        -- Number of Blocks per Region
        MFB_REG_SIZE     : natural := 1;
        -- Number of Items per Block
        MFB_BLOCK_SIZE   : natural := 8;
        -- Width of one MFB Item in bits
        MFB_ITEM_WIDTH   : natural := 32;
        -- Width of MFB metadata in bits
        MFB_META_WIDTH   : natural := 1;

        -- Add a skid slot in front of each MFB input register. It shortens the
        -- longest path at the cost of one more word of registers per input.
        IN_REG_SKID_EN   : boolean := false;

        -- MFB data payload enable for each input port, false leaves out its MFB path
        RX_PAYLOAD_EN    : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);

        -- Width of the stream switch timeout counter. One input is served for
        -- 2**(SW_TIMEOUT_WIDTH-1) MVB words, or until it runs out of headers.
        SW_TIMEOUT_WIDTH : natural := 4;
        -- Depth of the switch FIFO in items. It holds one item per packet
        -- whose header announced a payload.
        SW_FIFO_ITEMS    : natural := MVB_ITEMS*32;

        -- Architecture of the internal FIFOX_MULTI, "SHAKEDOWN" or "FULL"
        FIFOX_MULTI_ARCH : string  := "SHAKEDOWN";

        -- Target device family
        DEVICE           : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX INTERFACES (per input port)
        -- =====================================================================

        RX_MVB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_MVB_PAYLOAD : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MVB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        RX_MFB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MFB_SOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        -- =====================================================================
        -- TX INTERFACE (merged output)
        -- =====================================================================

        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER_FLAT is

    -- =========================================================================
    --  CONSTANTS
    -- =========================================================================

    constant SOF_POS_WIDTH  : natural := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH  : natural := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant MFB_DATA_WIDTH : natural := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant HDR_WIDTH      : natural := MVB_ITEM_WIDTH;

    constant CORR_SOF_POS_WIDTH : natural := log2(MFB_REG_SIZE);

    -- -------------------------------------------------------------------------
    -- Switch: which input the next packet on the output comes from
    -- -------------------------------------------------------------------------

    -- Width of one switch queue item, it holds the number of an input stream
    constant SW_WIDTH      : natural := max(1,log2(MERGER_INPUTS));
    -- Number of streams handed to MVB_MERGE_STREAMS. Its round-robin counter is
    -- log2(RX_STREAMS) bits wide and indexes the stream arrays directly. A count
    -- that is not a power of two would let the counter reach a stream that does
    -- not exist. The inputs are therefore padded to a power of two. The padding
    -- streams never claim to be ready, so the arbiter always skips them.
    constant SW_STREAMS    : natural := 2**SW_WIDTH;
    -- MVB item travelling through the stream merger: header, switch and payload
    constant MVB_DATA_W    : natural := HDR_WIDTH+SW_WIDTH+1;
    -- Offset of the switch and of the payload flag inside that item
    constant MVB_SW_O      : natural := HDR_WIDTH;
    constant MVB_PAYLOAD_O : natural := HDR_WIDTH+SW_WIDTH;

    -- Number of switch items the MFB sending logic inspects at once. Each item
    -- says which input the next packet comes from. That is one item per Region,
    -- plus one for a packet continuing from the previous word.
    constant SW_ITEMS       : natural := MFB_REGIONS+1;
    -- One item leaves per packet whose EOF is in the word, and a Region holds at
    -- most one EOF. This is therefore all the queue can lose in a cycle. It is
    -- also all the switch FIFO ever has to hand it.
    constant SW_WINDOW      : natural := MFB_REGIONS;
    -- Depth of the register queue holding the head of the switch FIFO. The queue
    -- is refilled by a whole window while it has room for one. Two windows would
    -- let it swing below a full window and throttle the output. Three windows
    -- always keep at least a full one in it.
    constant SW_QUEUE_ITEMS : natural := 3*SW_ITEMS;
    constant SW_QUEUE_CNT_W : natural := log2(SW_QUEUE_ITEMS+1);
    constant SW_CNT_W       : natural := log2(SW_ITEMS+1);

    -- =========================================================================
    --  FUNCTIONS
    -- =========================================================================

    -- True when the SOF of the given Region lies behind its EOF. The Region then
    -- ends one packet and starts the next one.
    function sof_after_eof_f (sof_pos, eof_pos : std_logic_vector; region : natural) return std_logic is
        constant SOF_MSB : natural := (region+1)*SOF_POS_WIDTH-1;
        constant EOF_MSB : natural := (region+1)*EOF_POS_WIDTH-1;
    begin
        if (unsigned(sof_pos(SOF_MSB downto SOF_MSB+1-CORR_SOF_POS_WIDTH)) >
            unsigned(eof_pos(EOF_MSB downto EOF_MSB+1-CORR_SOF_POS_WIDTH))) then
            return '1';
        end if;
        return '0';
    end function;

    -- Number of packets whose EOF lies in a word with these Region flags.
    function passed_cnt_f (vld, eof : std_logic_vector) return natural is
        variable cnt : natural := 0;
    begin
        for e in 0 to MFB_REGIONS-1 loop
            if (vld(e) = '1' and eof(e) = '1') then
                cnt := cnt + 1;
            end if;
        end loop;
        return cnt;
    end function;

    -- Number of packets present in a word with these Region flags, counting the
    -- one continuing from the previous word.
    function appeared_cnt_f (vld, sof, eof, saf : std_logic_vector) return natural is
        variable cnt : natural := 0;
    begin
        if (vld(0) = '1' and ((saf(0) = '1' and eof(0) = '1') or sof(0) = '0')) then
            cnt := 1;
        end if;

        for e in 0 to MFB_REGIONS-1 loop
            if (vld(e) = '1' and sof(e) = '1') then
                cnt := cnt + 1;
            end if;
        end loop;
        return cnt;
    end function;


    -- =========================================================================
    --  SIGNALS
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- RX side, before the input registers
    -- -------------------------------------------------------------------------


    -- RX MVB as it enters the merger
    signal rx_in_mvb_data    : slv_array_t(SW_STREAMS-1 downto 0)(MVB_ITEMS*MVB_DATA_W-1 downto 0) := (others => (others => '0'));
    signal rx_in_mvb_hdr     : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal rx_in_mvb_payload : slv_array_t(MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal rx_in_mvb_vld     : slv_array_t(SW_STREAMS-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => '0'));
    signal rx_in_mvb_src_rdy : std_logic_vector(SW_STREAMS-1 downto 0) := (others => '0');
    signal rx_in_mvb_dst_rdy : std_logic_vector(SW_STREAMS-1 downto 0);

    -- RX MFB as it enters the merger
    signal rx_in_mfb_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal rx_in_mfb_meta    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_in_mfb_sof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_in_mfb_eof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_in_mfb_sof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal rx_in_mfb_eof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal rx_in_mfb_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal rx_in_mfb_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- RX MFB with the per Region valid flags added
    signal rx_mfb_data_ext    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal rx_mfb_meta_ext    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal rx_mfb_sof_ext     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_eof_ext     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_sof_pos_ext : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_eof_pos_ext : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal rx_mfb_vld_ext     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal rx_mfb_src_rdy_ext : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal rx_mfb_dst_rdy_ext : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- SOF behind EOF in the incoming word, for the counts written along with it
    signal rx_mfb_saf_ext     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- -------------------------------------------------------------------------
    -- MFB input registers
    -- -------------------------------------------------------------------------

    signal mfb_input_data_reg    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0) := (others => (others => '0'));
    signal mfb_input_meta_reg    : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
    signal mfb_input_sof_reg     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal mfb_input_eof_reg     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal mfb_input_sof_pos_reg : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0) := (others => (others => '0'));
    signal mfb_input_eof_pos_reg : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0) := (others => (others => '0'));
    signal mfb_input_vld_reg     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0) := (others => (others => '0'));
    signal mfb_input_reg_vld     : std_logic_vector(MERGER_INPUTS-1 downto 0) := (others => '0');

    -- Register enables: read the word out, take a new one in, rewrite the flags
    signal mfb_input_reg_rd  : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal mfb_input_reg_wr  : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal mfb_input_reg_upd : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Flags the update writes back into the register
    signal mfb_input_update_eof : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_update_vld : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- Packet counts of the word held in the register, kept beside it
    signal mfb_input_passed_cnt_reg   : i_array_t(MERGER_INPUTS-1 downto 0) := (others => 0);
    signal mfb_input_appeared_cnt_reg : i_array_t(MERGER_INPUTS-1 downto 0) := (others => 0);

    -- Word offered to the input register, with its packet counts already worked
    -- out. It is the RX stream, or the skid slot when that one holds a word.
    signal mfb_input_src_data         : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal mfb_input_src_meta         : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_input_src_sof          : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_src_eof          : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_src_sof_pos      : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_input_src_eof_pos      : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_input_src_vld          : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal mfb_input_src_rdy          : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal mfb_input_src_passed_cnt   : i_array_t(MERGER_INPUTS-1 downto 0);
    signal mfb_input_src_appeared_cnt : i_array_t(MERGER_INPUTS-1 downto 0);

    -- The same counts per Region, and the SOF behind EOF flags they need
    signal mfb_input_pac_passed_cnti   : i_array_2d_t(MERGER_INPUTS-1 downto 0)(SW_ITEMS-1 downto 0) := (others => (others => 0));
    signal mfb_input_pac_appeared_cnti : i_array_2d_t(MERGER_INPUTS-1 downto 0)(SW_ITEMS-1 downto 0) := (others => (others => 0));
    signal mfb_sof_after_eof           : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- -------------------------------------------------------------------------
    -- MVB stream merger and switch FIFO
    -- -------------------------------------------------------------------------

    signal mvb_merge_tx_data    : std_logic_vector(MVB_ITEMS*MVB_DATA_W-1 downto 0);
    signal mvb_merge_tx_vld     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_merge_tx_src_rdy : std_logic;
    signal mvb_merge_tx_dst_rdy : std_logic;

    signal switch_fifoxm_di     : std_logic_vector(MVB_ITEMS*SW_WIDTH-1 downto 0);
    signal switch_fifoxm_wr     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_full   : std_logic;
    signal switch_fifoxm_do     : std_logic_vector(SW_WINDOW*SW_WIDTH-1 downto 0);
    signal switch_fifoxm_do_arr : slv_array_t(SW_WINDOW-1 downto 0)(SW_WIDTH-1 downto 0);
    signal switch_fifoxm_rd     : std_logic_vector(SW_WINDOW-1 downto 0);
    signal switch_fifoxm_empty  : std_logic_vector(SW_WINDOW-1 downto 0);

    -- -------------------------------------------------------------------------
    -- Switch queue: registered head of the switch FIFO
    -- -------------------------------------------------------------------------

    -- Switches taken out of the FIFO and held for a cycle before the queue
    -- appends them
    signal stage_data : slv_array_t(SW_WINDOW-1 downto 0)(SW_WIDTH-1 downto 0) := (others => (others => '0'));
    signal stage_vld  : std_logic_vector(SW_WINDOW-1 downto 0) := (others => '0');
    signal stage_cnt  : unsigned(SW_QUEUE_CNT_W-1 downto 0) := (others => '0');

    signal switch_q_data    : slv_array_t(SW_QUEUE_ITEMS-1 downto 0)(SW_WIDTH-1 downto 0) := (others => (others => '0'));
    signal switch_q_vld     : std_logic_vector(SW_QUEUE_ITEMS-1 downto 0) := (others => '0');
    signal switch_q_cnt     : unsigned(SW_QUEUE_CNT_W-1 downto 0) := (others => '0');
    signal switch_q_refill  : std_logic := '1';
    signal switch_q_rd_cnt  : unsigned(SW_QUEUE_CNT_W-1 downto 0);
    signal switch_q_wr_cnt  : unsigned(SW_QUEUE_CNT_W-1 downto 0);
    signal switch_q_cnt_app : unsigned(SW_QUEUE_CNT_W-1 downto 0);
    signal switch_q_cnt_new : unsigned(SW_QUEUE_CNT_W-1 downto 0);

    -- Queue after the append, and after the append and the read
    signal switch_q_app_data : slv_array_t(SW_QUEUE_ITEMS-1 downto 0)(SW_WIDTH-1 downto 0);
    signal switch_q_app_vld  : std_logic_vector(SW_QUEUE_ITEMS-1 downto 0);
    signal switch_q_data_new : slv_array_t(SW_QUEUE_ITEMS-1 downto 0)(SW_WIDTH-1 downto 0);
    signal switch_q_vld_new  : std_logic_vector(SW_QUEUE_ITEMS-1 downto 0);

    -- -------------------------------------------------------------------------
    -- MFB sending
    -- -------------------------------------------------------------------------

    -- Input selected by the head of the queue, and the run of packets that may
    -- be taken from it
    signal switch_currenti         : integer := 0;
    signal switch_run_len          : unsigned(SW_CNT_W-1 downto 0);
    signal switch_current_pac_cnti : integer := 0;

    -- Regions of the selected input that are loaded into the output word
    signal mfb_region_read_req : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);

    -- -------------------------------------------------------------------------
    -- TX side
    -- -------------------------------------------------------------------------

    -- New data for the MVB output register
    signal mvb_output_hdr         : std_logic_vector(MVB_ITEMS*HDR_WIDTH-1 downto 0);
    signal mvb_output_payload     : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_output_vld         : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_output_src_rdy     : std_logic;
    signal mvb_output_dst_rdy     : std_logic;

    -- New data for the MFB output register
    signal mfb_output_data    : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0);
    signal mfb_output_meta    : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal mfb_output_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_output_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal mfb_output_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal mfb_output_src_rdy : std_logic;
    signal mfb_output_dst_rdy : std_logic;

    -- =========================================================================
    --  ATTRIBUTES
    -- =========================================================================

    -- One bit of each of these enables a whole input word, so each drives more
    -- than a thousand flip-flops. The switch they are decoded from is on the
    -- longest path in the design. Replicating them puts a copy next to each group
    -- of loads instead of routing one net across the whole component.
    --
    -- Quartus replicates them on its own. A limit named there would only keep it
    -- from folding them into the register enables they feed. That leaves a level
    -- of logic on the path, so the limit is set for Vivado alone.
    attribute max_fanout : integer;
    attribute max_fanout of mfb_input_reg_rd  : signal is 16;
    attribute max_fanout of mfb_input_reg_wr  : signal is 16;
    attribute max_fanout of mfb_input_reg_upd : signal is 16;

begin

    assert (MERGER_INPUTS >= 2)
        report "MFB_MERGER_FLAT: Use MERGER_INPUTS of 2 or more."
        severity failure;

    -- =========================================================================
    --  1. RX INTERFACE
    -- =========================================================================
    -- A header of an input whose payload is disabled never announces one.

    rx_in_g : for i in 0 to MERGER_INPUTS-1 generate
        rx_in_mvb_hdr(i)     <= RX_MVB_DATA(i);
        rx_in_mvb_payload(i) <= RX_MVB_PAYLOAD(i) when RX_PAYLOAD_EN(i) else (others => '0');
        rx_in_mvb_vld(i)     <= RX_MVB_VLD(i);
        rx_in_mvb_src_rdy(i) <= RX_MVB_SRC_RDY(i);
        RX_MVB_DST_RDY(i)    <= rx_in_mvb_dst_rdy(i);

        rx_in_mfb_data(i)    <= RX_MFB_DATA(i);
        rx_in_mfb_meta(i)    <= RX_MFB_META(i);
        rx_in_mfb_sof(i)     <= RX_MFB_SOF(i);
        rx_in_mfb_eof(i)     <= RX_MFB_EOF(i);
        rx_in_mfb_sof_pos(i) <= RX_MFB_SOF_POS(i);
        rx_in_mfb_eof_pos(i) <= RX_MFB_EOF_POS(i);
        rx_in_mfb_src_rdy(i) <= RX_MFB_SRC_RDY(i);
        RX_MFB_DST_RDY(i)    <= rx_in_mfb_dst_rdy(i);
    end generate;

    -- =========================================================================
    --  2. RX MFB AUXILIARY SIGNALS
    -- =========================================================================

    rx_mfb_ext_g : for i in 0 to MERGER_INPUTS-1 generate
        rx_mfb_ext_i : entity work.MFB_AUXILIARY_SIGNALS
        generic map (
            REGIONS       => MFB_REGIONS,
            REGION_SIZE   => MFB_REG_SIZE,
            BLOCK_SIZE    => MFB_BLOCK_SIZE,
            ITEM_WIDTH    => MFB_ITEM_WIDTH,

            REGION_AUX_EN => true,
            BLOCK_AUX_EN  => false,
            ITEM_AUX_EN   => false
        )
        port map (
            CLK           => CLK,
            RESET         => RESET,

            RX_DATA       => rx_in_mfb_data(i),
            RX_SOF_POS    => rx_in_mfb_sof_pos(i),
            RX_EOF_POS    => rx_in_mfb_eof_pos(i),
            RX_SOF        => rx_in_mfb_sof(i),
            RX_EOF        => rx_in_mfb_eof(i),
            RX_SRC_RDY    => rx_in_mfb_src_rdy(i),
            RX_DST_RDY    => rx_in_mfb_dst_rdy(i),

            TX_DATA       => rx_mfb_data_ext(i),
            TX_SOF_POS    => rx_mfb_sof_pos_ext(i),
            TX_EOF_POS    => rx_mfb_eof_pos_ext(i),
            TX_SOF        => rx_mfb_sof_ext(i),
            TX_EOF        => rx_mfb_eof_ext(i),
            TX_REGION_VLD => rx_mfb_vld_ext(i),
            TX_SRC_RDY    => rx_mfb_src_rdy_ext(i),
            TX_DST_RDY    => rx_mfb_dst_rdy_ext(i)
        );

        rx_mfb_meta_ext(i) <= rx_in_mfb_meta(i);
    end generate;

    -- =========================================================================
    --  3. MFB INPUT REGISTERS
    -- =========================================================================
    -- Two packet counts are kept beside every word: how many packets end in it,
    -- and how many it holds at all. Comparing them with switch_run_len decides
    -- whether the word can go out in one piece.

    -- The incoming word needs the same SOF to EOF comparison as the one already
    -- held. Its packet counts are then written into the register along with it.
    rx_mfb_saf_ext_g : for i in 0 to MERGER_INPUTS-1 generate
        rx_mfb_saf_ext_reg_g : for e in 0 to MFB_REGIONS-1 generate
            rx_mfb_saf_ext(i)(e) <= sof_after_eof_f(rx_mfb_sof_pos_ext(i),rx_mfb_eof_pos_ext(i),e);
        end generate;
    end generate;

    mfb_input_reg_g : for i in 0 to MERGER_INPUTS-1 generate
        mfb_input_reg_pr : process (CLK)
        begin
            if (rising_edge(CLK)) then
                -- The whole word has been read out.
                if (mfb_input_reg_rd(i) = '1') then
                    mfb_input_reg_vld(i) <= '0';
                end if;

                -- Only part of the word has been read out. The Regions that
                -- left are struck off the flags of the word that stays.
                if (mfb_input_reg_upd(i) = '1') then
                    mfb_input_eof_reg(i) <= mfb_input_update_eof(i);
                    mfb_input_vld_reg(i) <= mfb_input_update_vld(i);

                    mfb_input_passed_cnt_reg(i)   <= passed_cnt_f(mfb_input_update_vld(i),mfb_input_update_eof(i));
                    mfb_input_appeared_cnt_reg(i) <= appeared_cnt_f(mfb_input_update_vld(i),mfb_input_sof_reg(i),mfb_input_update_eof(i),mfb_sof_after_eof(i));
                end if;

                -- A new word is taken in. This comes last, so it wins over the
                -- update of the word it replaces.
                if (mfb_input_reg_wr(i) = '1') then
                    mfb_input_data_reg(i)    <= mfb_input_src_data(i);
                    mfb_input_meta_reg(i)    <= mfb_input_src_meta(i);
                    mfb_input_sof_reg(i)     <= mfb_input_src_sof(i);
                    mfb_input_eof_reg(i)     <= mfb_input_src_eof(i);
                    mfb_input_sof_pos_reg(i) <= mfb_input_src_sof_pos(i);
                    mfb_input_eof_pos_reg(i) <= mfb_input_src_eof_pos(i);
                    mfb_input_vld_reg(i)     <= mfb_input_src_vld(i);
                    mfb_input_reg_vld(i)     <= mfb_input_src_rdy(i);

                    mfb_input_passed_cnt_reg(i)   <= mfb_input_src_passed_cnt(i);
                    mfb_input_appeared_cnt_reg(i) <= mfb_input_src_appeared_cnt(i);
                end if;

                if (RESET = '1') then
                    mfb_input_reg_vld(i) <= '0';
                end if;
            end if;
        end process;

        mfb_input_reg_wr(i) <= '1' when (mfb_input_reg_vld(i) = '0' or mfb_input_reg_rd(i) = '1') else '0';

        -- The RX stream feeds the register directly and the ready sent upstream
        -- is the register enable itself. That ready therefore carries the switch
        -- arbitration of this cycle out into the component in front.
        in_reg_skid_g : if (not IN_REG_SKID_EN) generate
            mfb_input_src_data(i)     <= rx_mfb_data_ext(i);
            mfb_input_src_meta(i)     <= rx_mfb_meta_ext(i);
            mfb_input_src_sof(i)      <= rx_mfb_sof_ext(i);
            mfb_input_src_eof(i)      <= rx_mfb_eof_ext(i);
            mfb_input_src_sof_pos(i)  <= rx_mfb_sof_pos_ext(i);
            mfb_input_src_eof_pos(i)  <= rx_mfb_eof_pos_ext(i);
            mfb_input_src_vld(i)      <= rx_mfb_vld_ext(i);
            mfb_input_src_rdy(i)      <= rx_mfb_src_rdy_ext(i);

            mfb_input_src_passed_cnt(i)   <= passed_cnt_f(rx_mfb_vld_ext(i),rx_mfb_eof_ext(i));
            mfb_input_src_appeared_cnt(i) <= appeared_cnt_f(rx_mfb_vld_ext(i),rx_mfb_sof_ext(i),rx_mfb_eof_ext(i),rx_mfb_saf_ext(i));

            rx_mfb_dst_rdy_ext(i) <= mfb_input_reg_wr(i);

        -- A word may instead wait in a skid slot beside the register. The slot is
        -- skipped whenever the register can take the word right away. It stays
        -- empty while the output flows and fills only when the switch stalls this
        -- input. What it buys is the ready below: a comparison of a two bit
        -- counter, which leaves the arbitration of this cycle inside the merger.
        else generate
            signal skid_data         : std_logic_vector(MFB_REGIONS*MFB_DATA_WIDTH-1 downto 0) := (others => '0');
            signal skid_meta         : std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
            signal skid_sof          : std_logic_vector(MFB_REGIONS-1 downto 0) := (others => '0');
            signal skid_eof          : std_logic_vector(MFB_REGIONS-1 downto 0) := (others => '0');
            signal skid_sof_pos      : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0) := (others => '0');
            signal skid_eof_pos      : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0) := (others => '0');
            signal skid_vld          : std_logic_vector(MFB_REGIONS-1 downto 0) := (others => '0');
            signal skid_passed_cnt   : natural := 0;
            signal skid_appeared_cnt : natural := 0;
            signal skid_reg_vld      : std_logic := '0';

            signal skid_wr           : std_logic;
            signal skid_data_wr      : std_logic;
            signal skid_rd           : std_logic;
            signal skid_bypass       : std_logic;

            -- Words held in the slot and the register together, 0 to 2
            signal fill_reg          : unsigned(1 downto 0) := (others => '0');
            signal word_taken        : std_logic;
            signal word_left         : std_logic;
        begin
            -- The register takes the RX word itself only when the slot has
            -- nothing to hand over first.
            skid_bypass  <= mfb_input_reg_wr(i) and (not skid_reg_vld);
            -- Only the valid bit takes the bypass into account, so the data
            -- register enables stay out of the arbitration. What they load on
            -- a bypass is never read. The multiplexer below reaches for the slot
            -- only while skid_reg_vld is set.
            skid_data_wr <= word_taken;
            skid_wr      <= word_taken and (not skid_bypass);
            skid_rd      <= skid_reg_vld and mfb_input_reg_wr(i);

            skid_reg_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (skid_rd = '1') then
                        skid_reg_vld <= '0';
                    end if;

                    if (skid_data_wr = '1') then
                        skid_data         <= rx_mfb_data_ext(i);
                        skid_meta         <= rx_mfb_meta_ext(i);
                        skid_sof          <= rx_mfb_sof_ext(i);
                        skid_eof          <= rx_mfb_eof_ext(i);
                        skid_sof_pos      <= rx_mfb_sof_pos_ext(i);
                        skid_eof_pos      <= rx_mfb_eof_pos_ext(i);
                        skid_vld          <= rx_mfb_vld_ext(i);

                        skid_passed_cnt   <= passed_cnt_f(rx_mfb_vld_ext(i),rx_mfb_eof_ext(i));
                        skid_appeared_cnt <= appeared_cnt_f(rx_mfb_vld_ext(i),rx_mfb_sof_ext(i),rx_mfb_eof_ext(i),rx_mfb_saf_ext(i));
                    end if;

                    if (skid_wr = '1') then
                        skid_reg_vld <= '1';
                    end if;

                    if (RESET = '1') then
                        skid_reg_vld <= '0';
                    end if;
                end if;
            end process;

            mfb_input_src_data(i)     <= skid_data     when (skid_reg_vld = '1') else rx_mfb_data_ext(i);
            mfb_input_src_meta(i)     <= skid_meta     when (skid_reg_vld = '1') else rx_mfb_meta_ext(i);
            mfb_input_src_sof(i)      <= skid_sof      when (skid_reg_vld = '1') else rx_mfb_sof_ext(i);
            mfb_input_src_eof(i)      <= skid_eof      when (skid_reg_vld = '1') else rx_mfb_eof_ext(i);
            mfb_input_src_sof_pos(i)  <= skid_sof_pos  when (skid_reg_vld = '1') else rx_mfb_sof_pos_ext(i);
            mfb_input_src_eof_pos(i)  <= skid_eof_pos  when (skid_reg_vld = '1') else rx_mfb_eof_pos_ext(i);
            mfb_input_src_vld(i)      <= skid_vld      when (skid_reg_vld = '1') else rx_mfb_vld_ext(i);
            mfb_input_src_rdy(i)      <= skid_reg_vld or rx_mfb_src_rdy_ext(i);

            mfb_input_src_passed_cnt(i)   <= skid_passed_cnt   when (skid_reg_vld = '1') else passed_cnt_f(rx_mfb_vld_ext(i),rx_mfb_eof_ext(i));
            mfb_input_src_appeared_cnt(i) <= skid_appeared_cnt when (skid_reg_vld = '1') else appeared_cnt_f(rx_mfb_vld_ext(i),rx_mfb_sof_ext(i),rx_mfb_eof_ext(i),rx_mfb_saf_ext(i));

            -- The read enable alone is not proof that a word left. It is asserted
            -- for the selected input even when that input holds nothing.
            word_taken <= rx_mfb_src_rdy_ext(i) and rx_mfb_dst_rdy_ext(i);
            word_left  <= mfb_input_reg_rd(i) and mfb_input_reg_vld(i);

            fill_reg_pr : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (word_taken = '1' and word_left = '0') then
                        fill_reg <= fill_reg + 1;
                    elsif (word_taken = '0' and word_left = '1') then
                        fill_reg <= fill_reg - 1;
                    end if;

                    if (RESET = '1') then
                        fill_reg <= (others => '0');
                    end if;
                end if;
            end process;

            rx_mfb_dst_rdy_ext(i) <= '1' when (fill_reg < 2) else '0';
        end generate;
    end generate;

    -- Packets whose EOF has already passed before each Region of the held word.
    pac_passed_cnt_pr : process (all)
        variable cnt : i_array_t(MERGER_INPUTS-1 downto 0);
    begin
        mfb_input_pac_passed_cnti <= (others => (others => 0));
        cnt                       := (others => 0);

        for i in 0 to MERGER_INPUTS-1 loop
            for e in 0 to MFB_REGIONS-1 loop
                mfb_input_pac_passed_cnti(i)(e) <= cnt(i);
                if (mfb_input_vld_reg(i)(e) = '1' and mfb_input_eof_reg(i)(e) = '1') then
                    cnt(i) := cnt(i)+1;
                end if;
            end loop;
            mfb_input_pac_passed_cnti(i)(MFB_REGIONS) <= cnt(i);
        end loop;
    end process;

    -- Packets that have started up to and including each Region of the held word.
    pac_appeared_cnt_pr : process (all)
        variable cnt : i_array_t(MERGER_INPUTS-1 downto 0);
    begin
        mfb_input_pac_appeared_cnti <= (others => (others => 0));
        cnt                         := (others => 0);

        for i in 0 to MERGER_INPUTS-1 loop
            -- the packet continuing from the previous word, if there is one
            if (mfb_input_vld_reg(i)(0) = '1'
                and ((mfb_sof_after_eof(i)(0) = '1' and mfb_input_eof_reg(i)(0) = '1') or mfb_input_sof_reg(i)(0) = '0')) then
                cnt(i) := cnt(i)+1;
            end if;

            for e in 0 to MFB_REGIONS-1 loop
                if (mfb_input_vld_reg(i)(e) = '1' and mfb_input_sof_reg(i)(e) = '1') then
                    cnt(i) := cnt(i)+1;
                end if;
                mfb_input_pac_appeared_cnti(i)(e) <= cnt(i);
            end loop;
            mfb_input_pac_appeared_cnti(i)(MFB_REGIONS) <= cnt(i);
        end loop;
    end process;

    mfb_sof_eof_cmp_g : for i in 0 to MERGER_INPUTS-1 generate
        mfb_sof_eof_cmp_reg_g : for e in 0 to MFB_REGIONS-1 generate
            mfb_sof_after_eof(i)(e) <= sof_after_eof_f(mfb_input_sof_pos_reg(i),mfb_input_eof_pos_reg(i),e);
        end generate;
    end generate;

    -- =========================================================================
    --  4. MVB SENDING
    -- =========================================================================
    -- The number of the input each header came from travels with it, and is what
    -- the MFB half follows.

    rx_in_mvb_data_g : for i in 0 to MERGER_INPUTS-1 generate
        rx_in_mvb_data_item_g : for e in 0 to MVB_ITEMS-1 generate
            rx_in_mvb_data(i)(e*MVB_DATA_W+HDR_WIDTH-1 downto e*MVB_DATA_W)                  <= rx_in_mvb_hdr(i)((e+1)*HDR_WIDTH-1 downto e*HDR_WIDTH);
            rx_in_mvb_data(i)(e*MVB_DATA_W+MVB_SW_O+SW_WIDTH-1 downto e*MVB_DATA_W+MVB_SW_O) <= std_logic_vector(to_unsigned(i,SW_WIDTH));
            rx_in_mvb_data(i)(e*MVB_DATA_W+MVB_PAYLOAD_O)                                    <= rx_in_mvb_payload(i)(e);
        end generate;
    end generate;

    mvb_merge_st_i : entity work.MVB_MERGE_STREAMS
    generic map (
        MVB_ITEMS       => MVB_ITEMS,
        MVB_ITEM_WIDTH  => MVB_DATA_W, -- payload & switch & header
        RX_STREAMS      => SW_STREAMS,
        RX_SHAKEDOWN_EN => True,
        SW_TIMEOUT_W    => SW_TIMEOUT_WIDTH,
        DEVICE          => DEVICE
    )
    port map (
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => rx_in_mvb_data,
        RX_VLD     => rx_in_mvb_vld,
        RX_SRC_RDY => rx_in_mvb_src_rdy,
        RX_DST_RDY => rx_in_mvb_dst_rdy,

        TX_DATA    => mvb_merge_tx_data,
        TX_VLD     => mvb_merge_tx_vld,
        TX_SRC_RDY => mvb_merge_tx_src_rdy,
        TX_DST_RDY => mvb_merge_tx_dst_rdy
    );

    mvb_merge_tx_g : for i in 0 to MVB_ITEMS-1 generate
        mvb_output_hdr((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH) <= mvb_merge_tx_data(i*MVB_DATA_W+HDR_WIDTH-1 downto i*MVB_DATA_W);
        mvb_output_payload(i)                                <= mvb_merge_tx_data(i*MVB_DATA_W+MVB_PAYLOAD_O);

    end generate;

    -- A header may only leave once its switch is safely in the FIFO. Otherwise
    -- the MFB side would never learn where its payload is.
    mvb_output_vld       <= mvb_merge_tx_vld;
    mvb_output_src_rdy   <= mvb_merge_tx_src_rdy and (not switch_fifoxm_full);
    mvb_merge_tx_dst_rdy <= mvb_output_dst_rdy and (not switch_fifoxm_full);

    -- =========================================================================
    --  5. SWITCH DECISION FIFO
    -- =========================================================================
    -- Holds one item per packet: the number of the input that packet comes from,
    -- in the order the packets leave on MVB. It has to be a FIFOX_MULTI because
    -- both ends move by more than one item a cycle.

    switch_fifoxm_in_g : for i in 0 to MVB_ITEMS-1 generate
        switch_fifoxm_di((i+1)*SW_WIDTH-1 downto i*SW_WIDTH) <= mvb_merge_tx_data(i*MVB_DATA_W+MVB_SW_O+SW_WIDTH-1 downto i*MVB_DATA_W+MVB_SW_O);

        -- Only a header that really leaves, and really has a payload, adds a
        -- switch for the MFB side.
        switch_fifoxm_wr(i) <= mvb_merge_tx_src_rdy
                               and mvb_merge_tx_vld(i)
                               and mvb_merge_tx_data(i*MVB_DATA_W+MVB_PAYLOAD_O)
                               and mvb_output_dst_rdy;
    end generate;

    switch_fifoxm_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH       => SW_WIDTH,
        ITEMS            => SW_FIFO_ITEMS,
        WRITE_PORTS      => MVB_ITEMS,
        READ_PORTS       => SW_WINDOW,
        RAM_TYPE         => "AUTO",
        SAFE_READ_MODE   => false,
        DEVICE           => DEVICE,
        FIFOX_MULTI_ARCH => FIFOX_MULTI_ARCH
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        DI    => switch_fifoxm_di,
        WR    => switch_fifoxm_wr,
        FULL  => switch_fifoxm_full,
        DO    => switch_fifoxm_do,
        RD    => switch_fifoxm_rd,
        EMPTY => switch_fifoxm_empty
    );

    switch_fifoxm_do_arr <= slv_array_deser(switch_fifoxm_do,SW_WINDOW);

    -- =========================================================================
    --  6. SWITCH QUEUE
    -- =========================================================================
    -- Holds the head of the switch FIFO in registers, so the scan below starts
    -- at registers. Reading that head straight out of FIFOX_MULTI would close a
    -- combinational loop through the scan and back into the FIFO reads.

    -- -------------------------------------------------------------------------
    -- Refilling from the FIFO
    -- -------------------------------------------------------------------------

    -- Refill by a whole window whenever the queue has room for it. The room is
    -- decided from the fill of the next cycle and held in a register. Neither the
    -- reads nor their count therefore wait for the fill of this cycle. The
    -- registered answer is the same, only reached a cycle earlier. It never
    -- depends on what the MFB logic decides now.
    switch_q_refill_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (switch_q_cnt_new <= SW_QUEUE_ITEMS-SW_WINDOW) then
                switch_q_refill <= '1';
            else
                switch_q_refill <= '0';
            end if;

            if (RESET = '1') then
                switch_q_refill <= '1';
            end if;
        end if;
    end process;

    -- Room in the queue is the only condition of a read, and it is already held
    -- in a register. Nothing but that register therefore stands in front of the
    -- read enables, which have to reach across to the FIFO.
    switch_fifoxm_rd_g : for i in 0 to SW_WINDOW-1 generate
        switch_fifoxm_rd(i) <= switch_q_refill and (not switch_fifoxm_empty(i));
    end generate;

    -- The FIFO is read into this register and the queue appends out of it.
    -- Neither the read mask nor its sum therefore stands between the FIFO and
    -- the fill of the queue. The register is appended and refilled
    -- in the same cycle, so it takes a fresh window every cycle. The queue never
    -- waits for one. The read mask is a set of leading ones, so a plain sum
    -- gives its length.
    stage_pr : process (CLK)
        variable wr_cnt : unsigned(SW_QUEUE_CNT_W-1 downto 0);
    begin
        if (rising_edge(CLK)) then
            if (switch_q_refill = '1') then
                wr_cnt := (others => '0');

                for i in 0 to SW_WINDOW-1 loop
                    if (switch_fifoxm_rd(i) = '1') then
                        wr_cnt := wr_cnt + 1;
                    end if;
                end loop;

                stage_data <= switch_fifoxm_do_arr;
                stage_vld  <= switch_fifoxm_rd;
                stage_cnt  <= wr_cnt;
            end if;

            if (RESET = '1') then
                stage_vld <= (others => '0');
                stage_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- Nothing is appended in a cycle the queue has no room for a whole window.
    switch_q_wr_cnt <= stage_cnt when (switch_q_refill = '1') else (others => '0');

    -- -------------------------------------------------------------------------
    -- Appending, reading and the new queue
    -- -------------------------------------------------------------------------

    -- Number of items taken from the head of the queue. That is one per packet
    -- whose EOF is leaving in this word, capped by switch_run_len. Taking the
    -- smaller bound directly keeps the read count one level away from the scan.
    -- The alternative puts it behind a mask and a sum of that mask.
    switch_q_rd_cnt_pr : process (all)
        variable rd_cnt : natural;
    begin
        rd_cnt := switch_current_pac_cnti;

        if (mfb_input_passed_cnt_reg(switch_currenti) < rd_cnt) then
            rd_cnt := mfb_input_passed_cnt_reg(switch_currenti);
        end if;

        -- nothing is read unless the output takes the word and the input holds one
        if (mfb_output_dst_rdy = '0' or mfb_input_reg_vld(switch_currenti) = '0') then
            rd_cnt := 0;
        end if;

        switch_q_rd_cnt <= to_unsigned(rd_cnt,SW_QUEUE_CNT_W);
    end process;

    -- New items from the FIFO are appended at the tail of the queue. That position
    -- follows the registered fill alone, so the append is ready long before the
    -- read count arrives.
    switch_q_app_pr : process (all)
    begin
        switch_q_app_data <= (others => (others => '0'));

        for i in 0 to SW_QUEUE_ITEMS-1 loop
            if (i < to_integer(switch_q_cnt)) then
                switch_q_app_data(i) <= switch_q_data(i);
            end if;

            for e in 0 to SW_WINDOW-1 loop
                if (i = e+to_integer(switch_q_cnt) and stage_vld(e) = '1' and switch_q_refill = '1') then
                    switch_q_app_data(i) <= stage_data(e);
                end if;
            end loop;
        end loop;
    end process;

    -- Fill of the appended queue and the valid bits that go with it. Both follow
    -- the registered fill alone, like the appended data above.
    switch_q_cnt_app <= switch_q_cnt + switch_q_wr_cnt;

    switch_q_app_vld_g : for i in 0 to SW_QUEUE_ITEMS-1 generate
        switch_q_app_vld(i) <= '1' when (i < switch_q_cnt_app) else '0';
    end generate;

    -- Items read from the queue leave at its head. Shifting the already appended
    -- queue leaves only one shifter on the path from the read count. The valid
    -- bits are shifted the same way, not derived from the new fill. Deriving
    -- them would put the whole count arithmetic behind that read count.
    switch_q_new_pr : process (all)
    begin
        switch_q_data_new <= (others => (others => '0'));
        switch_q_vld_new  <= (others => '0');

        for i in 0 to SW_QUEUE_ITEMS-1 loop
            if (i+to_integer(switch_q_rd_cnt) < SW_QUEUE_ITEMS) then
                switch_q_data_new(i) <= switch_q_app_data(i+to_integer(switch_q_rd_cnt));
                switch_q_vld_new(i)  <= switch_q_app_vld(i+to_integer(switch_q_rd_cnt));
            end if;
        end loop;
    end process;

    switch_q_cnt_new <= switch_q_cnt_app - switch_q_rd_cnt;

    switch_q_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            switch_q_data <= switch_q_data_new;
            switch_q_vld  <= switch_q_vld_new;
            switch_q_cnt  <= switch_q_cnt_new;

            if (RESET = '1') then
                switch_q_vld <= (others => '0');
                switch_q_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    --  7. MFB SENDING
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- Selected input and how much of it may be sent
    -- -------------------------------------------------------------------------

    -- Count how many switches at the head of the queue name the same input.
    -- Packets from other inputs must wait their turn. This run is therefore the
    -- most that can be taken from the selected input in this word.
    switch_info_pr : process (all)
    begin
        switch_run_len <= (others => '0');

        for i in 0 to SW_ITEMS-1 loop
            exit when (switch_q_vld(i) = '0' or switch_q_data(i) /= switch_q_data(0));
            switch_run_len <= to_unsigned(i+1,SW_CNT_W);
        end loop;
    end process;

    -- The queue only ever holds numbers of real inputs. MERGER_INPUTS need not be
    -- a power of two, so the switch can encode inputs that do not exist. Mask those codes off to keep the multiplexer index below in range.
    -- With a power-of-two MERGER_INPUTS the condition is always true and costs
    -- nothing.
    switch_currenti         <= to_integer(unsigned(switch_q_data(0))) when (unsigned(switch_q_data(0)) < MERGER_INPUTS) else 0;
    switch_current_pac_cnti <= to_integer(switch_run_len);

    -- A Region is read when it belongs to the selected input. Its packet must
    -- also be within the run that may be sent now.
    mfb_region_read_req_g : for i in 0 to MERGER_INPUTS-1 generate
        mfb_region_read_req_reg_g : for e in 0 to MFB_REGIONS-1 generate
            mfb_region_read_req(i)(e) <= '1' when (switch_currenti = i and switch_current_pac_cnti > mfb_input_pac_passed_cnti(i)(e)) else '0';
        end generate;
    end generate;

    -- -------------------------------------------------------------------------
    -- Output word
    -- -------------------------------------------------------------------------

    -- Data and positions come straight from the selected input register.
    mfb_output_data    <= mfb_input_data_reg(switch_currenti);
    mfb_output_meta    <= mfb_input_meta_reg(switch_currenti);
    mfb_output_sof_pos <= mfb_input_sof_pos_reg(switch_currenti);
    mfb_output_eof_pos <= mfb_input_eof_pos_reg(switch_currenti);

    -- Only the selected input ever requests a read, so its request alone says
    -- whether a Region is loaded.
    mfb_output_sof_eof_g : for e in 0 to MFB_REGIONS-1 generate
        -- The Region is loaded and holds a valid SOF. The packet that SOF starts
        -- is still within the run that may be sent.
        mfb_output_sof(e) <= '1' when (mfb_region_read_req(switch_currenti)(e) = '1'
                                       and mfb_input_vld_reg(switch_currenti)(e) = '1'
                                       and mfb_input_sof_reg(switch_currenti)(e) = '1'
                                       and switch_current_pac_cnti >= mfb_input_pac_appeared_cnti(switch_currenti)(e)) else
                             '0';

        -- The Region is loaded and holds a valid EOF.
        mfb_output_eof(e) <= '1' when (mfb_region_read_req(switch_currenti)(e) = '1'
                                       and mfb_input_vld_reg(switch_currenti)(e) = '1'
                                       and mfb_input_eof_reg(switch_currenti)(e) = '1') else
                             '0';
    end generate;

    -- The output word is valid once the switch says where to take it from. That
    -- input must also hold a word.
    mfb_output_src_rdy <= '1' when (switch_q_vld(0) = '1' and mfb_input_reg_vld(switch_currenti) = '1') else '0';

    -- -------------------------------------------------------------------------
    -- Input register control
    -- -------------------------------------------------------------------------

    -- What is left in the input register after the Regions that were read leave.
    mfb_input_update_g : for i in 0 to MERGER_INPUTS-1 generate
        mfb_input_update_reg_g : for e in 0 to MFB_REGIONS-1 generate
            -- A Region that was read no longer ends a packet.
            mfb_input_update_eof(i)(e) <= '0' when (mfb_region_read_req(i)(e) = '1') else
                                          mfb_input_eof_reg(i)(e);

            -- A Region that was read stays valid only when it starts a packet
            -- beyond the run that may be sent. That packet is left behind.
            mfb_input_update_vld(i)(e) <= '0' when (mfb_region_read_req(i)(e) = '1'
                                                    and (mfb_input_sof_reg(i)(e) = '0'
                                                         or switch_current_pac_cnti >= mfb_input_pac_appeared_cnti(i)(e))) else
                                          mfb_input_vld_reg(i)(e);
        end generate;
    end generate;

    -- Both terms below are already gated by the input being the selected one.
    -- They therefore read the packet counters of that input directly, not
    -- through the multiplexer of the selected one. Same result, one multiplexer
    -- less in front of the register enables.
    mfb_send_ctrl_g : for i in 0 to MERGER_INPUTS-1 generate
        -- Read the whole word out when every packet in it may be sent now.
        mfb_input_reg_rd(i) <= '1' when (switch_currenti = i
                                         and switch_current_pac_cnti >= mfb_input_appeared_cnt_reg(i)
                                         and mfb_output_dst_rdy = '1'
                                         and switch_q_vld(0) = '1') else
                               '0';

        -- The update enable does not depend on the input. It is kept a vector so
        -- that the fanout attribute above can give each input its own copy.
        mfb_input_reg_upd(i) <= '1' when (mfb_output_dst_rdy = '1' and switch_q_vld(0) = '1') else
                                '0';
    end generate;

    -- =========================================================================
    --  8. TX INTERFACE
    -- =========================================================================
    TX_MVB_DATA        <= mvb_output_hdr;
    TX_MVB_PAYLOAD     <= mvb_output_payload;
    TX_MVB_VLD         <= mvb_output_vld;
    TX_MVB_SRC_RDY     <= mvb_output_src_rdy;
    mvb_output_dst_rdy <= TX_MVB_DST_RDY;

    TX_MFB_DATA        <= mfb_output_data;
    TX_MFB_META        <= mfb_output_meta;
    TX_MFB_SOF         <= mfb_output_sof;
    TX_MFB_EOF         <= mfb_output_eof;
    TX_MFB_SOF_POS     <= mfb_output_sof_pos;
    TX_MFB_EOF_POS     <= mfb_output_eof_pos;
    TX_MFB_SRC_RDY     <= mfb_output_src_rdy;
    mfb_output_dst_rdy <= TX_MFB_DST_RDY;

end architecture;
