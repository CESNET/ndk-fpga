-- mfb_compactor.vhd: removes empty regions between MFB frames so that
--                    occupied regions become contiguous
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The MFB_COMPACTOR removes empty (unoccupied) regions between frames on the
-- MFB bus and shifts the occupied regions left so they are contiguous in the
-- output word, while preserving frame order and region order within a frame.
-- A region moves as one indivisible unit, so anything short of a whole idle
-- region is left untouched: an internally incomplete region (EOF_POS < max)
-- is not a gap, and neither is a region shared between the tail of one frame
-- and the head of the next (SOF_POS > EOF_POS within it) - only whole idle
-- regions between frames get removed. A small accumulator (up to REGIONS-1
-- leftover regions) holds regions that did not fill a whole output word yet;
-- it is combined with the next input word every cycle, so throughput is a
-- full word per cycle with no extra write port needed on any downstream
-- memory.
--
-- Occupancy (which regions carry frame data, including "the frame continues
-- through this whole word with no SOF/EOF") is derived with
-- MFB_AUXILIARY_SIGNALS's region-level in-frame carry. That carry correctly
-- follows a region shared between two frames as well as a fully aligned one,
-- so REGION_SIZE>1 works for arbitrary, non-region-aligned frame lengths too
-- - the only real constraint is plain MFB: a single region carries at most
-- one SOF and one EOF.
--
-- RX data falls through into the pipeline by default (see FWFT_MODE), so a
-- stalled TX_DST_RDY does not needlessly stall RX too while the accumulator
-- still has room.
--
entity MFB_COMPACTOR is
    generic (
        -- Number of regions in a word.
        REGIONS       : natural := 4;
        -- Number of blocks in a region.
        REGION_SIZE   : natural := 1;
        -- Number of items in a block.
        BLOCK_SIZE    : natural := 8;
        -- Width of one item, in bits.
        ITEM_WIDTH    : natural := 32;
        -- Width of optional per-region user metadata (0 = unused). Travels
        -- with its region through compaction.
        META_WIDTH    : natural := 0;
        -- Number of consecutive idle (no new occupied region) clock cycles
        -- after which a non-empty but not-yet-full accumulator is flushed to
        -- TX. 0 = flush as soon as no new data arrived on RX in the previous
        -- cycle (lowest latency, lowest density on bursty traffic); a larger
        -- value trades tail latency for a higher chance of fully packed
        -- output words. A flush only ever happens at a frame boundary: while
        -- the accumulator ends inside an unfinished frame it keeps waiting,
        -- because the padding of a partial word would read as that frame
        -- continuing.
        FLUSH_TIMEOUT : natural := 8;
        -- Insert a registered input stage ahead of the compaction logic.
        -- Useful for timing closure (isolates upstream routing/hard IP from
        -- the compaction/accumulator critical path); adds one clock cycle of
        -- latency.
        USE_PIPE      : boolean := true;
        -- First Word Fall Through mode. If FWFT_MODE=True, RX data keeps
        -- falling through into the pipeline whenever no valid TX word is
        -- waiting to be accepted yet, i.e. RX_DST_RDY='1' when TX_DST_RDY='1'
        -- OR TX_SRC_RDY='0', which spends the accumulator's already
        -- provisioned one-word slack instead of stalling RX the instant TX
        -- backpressures. If FWFT_MODE=False, RX_DST_RDY is the plain
        -- TX_DST_RDY wire; use it when the extra gate on RX_DST_RDY's wide
        -- fan-out does not fit the timing budget of whatever drives this
        -- component (e.g. a hard IP ready line).
        FWFT_MODE     : boolean := true
    );
    port (
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- =====================================================================
        -- RX MFB INTERFACE (uncompacted)
        -- =====================================================================
        RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- User metadata valid with its region.
        RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
        RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        -- TX MFB INTERFACE (compacted: no empty region between two occupied ones)
        -- =====================================================================
        TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_COMPACTOR is

    constant REGION_WIDTH    : natural := REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    constant SOF_POS_WIDTH   : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH   : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    -- Width of an input region index, used by the compaction multiplexers.
    constant SEL_WIDTH       : natural := max(1,log2(REGIONS));
    -- A whole word is emitted as soon as REGIONS regions are available, so the
    -- accumulator never has to hold more than REGIONS-1 of them.
    constant ACC_REGIONS     : natural := REGIONS-1;
    -- Accumulator plus one full input word: the most that is ever merged in a
    -- single clock cycle.
    constant MERGED_REGIONS  : natural := 2*REGIONS-1;
    -- Common width of all region counters, holds 0 .. MERGED_REGIONS.
    constant CNT_WIDTH       : natural := max(1,log2(2*REGIONS));
    constant FLUSH_CNT_WIDTH : natural := max(1,log2(FLUSH_TIMEOUT+1));

    -- Global clock enable: the whole pipeline (input register, compaction,
    -- accumulator, flush counter) advances only on s_ce, and RX_DST_RDY = s_ce.
    -- There is no combinational SRC_RDY/DST_RDY loop either way.
    signal s_ce : std_logic;

    -- Optional input register stage.
    signal s_rx_data    : std_logic_vector(REGIONS*REGION_WIDTH-1 downto 0);
    signal s_rx_meta    : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal s_rx_sof_pos : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal s_rx_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal s_rx_src_rdy : std_logic;

    signal s_rx_data_arr    : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_rx_meta_arr    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_rx_sof_pos_arr : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_rx_eof_pos_arr : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    -- Region carries data of some frame, including a frame that has neither
    -- SOF nor EOF in this word.
    signal s_region_vld : std_logic_vector(REGIONS-1 downto 0);
    signal s_region_occ : std_logic_vector(REGIONS-1 downto 0);

    -- Compaction control: which input region feeds each output position, and
    -- whether that position is used at all.
    signal s_sel_idx : u_array_t(REGIONS-1 downto 0)(SEL_WIDTH-1 downto 0);
    signal s_sel_vld : std_logic_vector(REGIONS-1 downto 0);

    -- Occupied regions of the input word, left-packed (order preserved), and
    -- how many of them there are.
    signal s_dense_data    : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_dense_meta    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_dense_sof_pos : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_dense_eof_pos : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_dense_sof     : std_logic_vector(REGIONS-1 downto 0);
    signal s_dense_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal s_dense_cnt     : unsigned(CNT_WIDTH-1 downto 0);

    signal s_dense_data_reg    : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_dense_meta_reg    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_dense_sof_pos_reg : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_dense_eof_pos_reg : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_dense_sof_reg     : std_logic_vector(REGIONS-1 downto 0);
    signal s_dense_eof_reg     : std_logic_vector(REGIONS-1 downto 0);
    signal s_dense_cnt_reg     : unsigned(CNT_WIDTH-1 downto 0);

    -- A frame is still open after the last region accepted so far.
    signal s_frame_open : std_logic;
    signal s_acc_open   : std_logic;

    -- Regions left over from previous cycles, waiting for a full word.
    signal s_acc_data    : slv_array_t(ACC_REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_acc_meta    : slv_array_t(ACC_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_acc_sof_pos : slv_array_t(ACC_REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_acc_eof_pos : slv_array_t(ACC_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_acc_sof     : std_logic_vector(ACC_REGIONS-1 downto 0);
    signal s_acc_eof     : std_logic_vector(ACC_REGIONS-1 downto 0);
    signal s_acc_fill    : unsigned(CNT_WIDTH-1 downto 0);

    -- The accumulator and the new input word concatenated into one dense list.
    signal s_merged_data    : slv_array_t(MERGED_REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_merged_meta    : slv_array_t(MERGED_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_merged_sof_pos : slv_array_t(MERGED_REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_merged_eof_pos : slv_array_t(MERGED_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_merged_sof     : std_logic_vector(MERGED_REGIONS-1 downto 0);
    signal s_merged_eof     : std_logic_vector(MERGED_REGIONS-1 downto 0);
    signal s_merged_cnt     : unsigned(CNT_WIDTH-1 downto 0);

    signal s_emit_word : std_logic;
    signal s_emit_part : std_logic;

    signal s_flush_cnt : unsigned(FLUSH_CNT_WIDTH-1 downto 0);
    signal s_flush_req : std_logic;

    signal s_tx_data_arr    : slv_array_t(REGIONS-1 downto 0)(REGION_WIDTH-1 downto 0);
    signal s_tx_meta_arr    : slv_array_t(REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal s_tx_sof_pos_arr : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal s_tx_eof_pos_arr : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_tx_sof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_tx_eof         : std_logic_vector(REGIONS-1 downto 0);
    signal s_tx_src_rdy     : std_logic;

begin

    -- =========================================================================
    --  FLOW CONTROL
    -- =========================================================================

    -- In FWFT mode the pipeline also advances when the TX word register is
    -- still empty, so RX data falls through into the accumulator without
    -- waiting for TX_DST_RDY.
    fwft_mode_g : if FWFT_MODE generate
        s_ce <= TX_DST_RDY or not s_tx_src_rdy;
    else generate
        s_ce <= TX_DST_RDY;
    end generate;

    RX_DST_RDY <= s_ce;

    -- =========================================================================
    --  INPUT REGISTER STAGE
    -- =========================================================================

    use_pipe_g : if USE_PIPE generate
        input_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_ce = '1') then
                    s_rx_data    <= RX_DATA;
                    s_rx_meta    <= RX_META;
                    s_rx_sof_pos <= RX_SOF_POS;
                    s_rx_eof_pos <= RX_EOF_POS;
                    s_rx_sof     <= RX_SOF;
                    s_rx_eof     <= RX_EOF;
                    s_rx_src_rdy <= RX_SRC_RDY;
                end if;
                if (RESET = '1') then
                    s_rx_src_rdy <= '0';
                end if;
            end if;
        end process;
    else generate
        s_rx_data    <= RX_DATA;
        s_rx_meta    <= RX_META;
        s_rx_sof_pos <= RX_SOF_POS;
        s_rx_eof_pos <= RX_EOF_POS;
        s_rx_sof     <= RX_SOF;
        s_rx_eof     <= RX_EOF;
        s_rx_src_rdy <= RX_SRC_RDY;
    end generate;

    s_rx_data_arr    <= slv_array_deser(s_rx_data,REGIONS,REGION_WIDTH);
    s_rx_meta_arr    <= slv_array_deser(s_rx_meta,REGIONS,META_WIDTH);
    s_rx_sof_pos_arr <= slv_array_deser(s_rx_sof_pos,REGIONS,SOF_POS_WIDTH);
    s_rx_eof_pos_arr <= slv_array_deser(s_rx_eof_pos,REGIONS,EOF_POS_WIDTH);

    -- =========================================================================
    --  0. STAGE: REGION OCCUPANCY AND COMPACTION
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- REGION OCCUPANCY
    -- -------------------------------------------------------------------------
    -- Reuses the in-frame carry already implemented by MFB_AUXILIARY_SIGNALS
    -- instead of duplicating it here.

    aux_signals_i : entity work.MFB_AUXILIARY_SIGNALS
    generic map (
        REGIONS       => REGIONS,
        REGION_SIZE   => REGION_SIZE,
        BLOCK_SIZE    => BLOCK_SIZE,
        ITEM_WIDTH    => ITEM_WIDTH,
        META_WIDTH    => 0,

        REGION_AUX_EN => True,
        BLOCK_AUX_EN  => False,
        ITEM_AUX_EN   => False
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => s_rx_data,
        RX_SOF_POS => s_rx_sof_pos,
        RX_EOF_POS => s_rx_eof_pos,
        RX_SOF     => s_rx_sof,
        RX_EOF     => s_rx_eof,
        RX_SRC_RDY => s_rx_src_rdy,
        RX_DST_RDY => open,

        TX_DATA    => open,
        TX_META    => open,
        TX_SOF_POS => open,
        TX_EOF_POS => open,
        TX_SOF     => open,
        TX_EOF     => open,
        TX_SRC_RDY => open,
        TX_DST_RDY => s_ce,

        TX_REGION_SHARED => open,
        TX_REGION_VLD    => s_region_vld,
        TX_BLOCK_VLD     => open,
        TX_ITEM_VLD      => open
    );

    -- Nothing is occupied on an invalid word. The carry state itself is
    -- untouched, MFB_AUXILIARY_SIGNALS only updates it on an accepted word.
    s_region_occ <= s_region_vld and (REGIONS-1 downto 0 => s_rx_src_rdy);

    -- -------------------------------------------------------------------------
    -- COMPACTION CONTROL
    -- -------------------------------------------------------------------------
    -- Assigns the occupied regions to the lowest output positions, keeping
    -- their order and dropping the idle ones in between. Index arithmetic
    -- only, the regions themselves are moved by the multiplexers below.

    compact_sel_p : process (all)
        variable v_idx : u_array_t(REGIONS-1 downto 0)(SEL_WIDTH-1 downto 0);
        variable v_vld : std_logic_vector(REGIONS-1 downto 0);
        variable v_cnt : natural range 0 to REGIONS;
    begin
        v_idx := (others => (others => '0'));
        v_vld := (others => '0');
        v_cnt := 0;

        for r in 0 to REGIONS-1 loop
            if (s_region_occ(r) = '1') then
                v_idx(v_cnt) := to_unsigned(r,SEL_WIDTH);
                v_vld(v_cnt) := '1';
                v_cnt        := v_cnt + 1;
            end if;
        end loop;

        s_sel_idx   <= v_idx;
        s_sel_vld   <= v_vld;
        s_dense_cnt <= to_unsigned(v_cnt,CNT_WIDTH);
    end process;

    -- -------------------------------------------------------------------------
    -- COMPACTION DATAPATH
    -- -------------------------------------------------------------------------
    -- Only SOF/EOF have to be cleared on an unused output position: that is
    -- what keeps a partially filled output word free of spurious frame starts
    -- and ends. Data and the POS fields of an unoccupied region are don't care
    -- on the MFB bus.

    compact_mux_g : for o in 0 to REGIONS-1 generate
        s_dense_data(o)    <= s_rx_data_arr(to_integer(s_sel_idx(o)));
        s_dense_meta(o)    <= s_rx_meta_arr(to_integer(s_sel_idx(o)));
        s_dense_sof_pos(o) <= s_rx_sof_pos_arr(to_integer(s_sel_idx(o)));
        s_dense_eof_pos(o) <= s_rx_eof_pos_arr(to_integer(s_sel_idx(o)));
        s_dense_sof(o)     <= s_rx_sof(to_integer(s_sel_idx(o))) and s_sel_vld(o);
        s_dense_eof(o)     <= s_rx_eof(to_integer(s_sel_idx(o))) and s_sel_vld(o);
    end generate;

    compaction_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_ce = '1') then
                s_dense_data_reg    <= s_dense_data;
                s_dense_meta_reg    <= s_dense_meta;
                s_dense_sof_pos_reg <= s_dense_sof_pos;
                s_dense_eof_pos_reg <= s_dense_eof_pos;
                s_dense_sof_reg     <= s_dense_sof;
                s_dense_eof_reg     <= s_dense_eof;
                s_dense_cnt_reg     <= s_dense_cnt;
            end if;
            if (RESET = '1') then
                s_dense_cnt_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    -- FRAME BOUNDARY TRACKING
    -- -------------------------------------------------------------------------
    -- Whether a frame is left open after the last accepted word. Compaction
    -- only drops idle regions, which are outside any frame, so the region
    -- order and this state are the same before and after it. A region carrying
    -- both SOF and EOF is ambiguous on its own - a frame contained in that one
    -- region, or a region shared between an ending frame and a new one that
    -- continues past it - so only a lone SOF or a lone EOF flips the state.
    --
    -- This register updates on the same clock edge as the compaction register
    -- below, so it already lines up with the word being merged. Pipelining it
    -- once more would make the accumulator look closed for one cycle after it
    -- took over an unfinished frame, which FLUSH_TIMEOUT=0 turns into exactly
    -- the cut frame this state exists to prevent.

    frame_open_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_ce = '1' and s_rx_src_rdy = '1') then
                for r in 0 to REGIONS-1 loop
                    if (s_rx_sof(r) = '1' and s_rx_eof(r) = '0') then
                        s_frame_open <= '1';
                    elsif (s_rx_eof(r) = '1' and s_rx_sof(r) = '0') then
                        s_frame_open <= '0';
                    end if;
                end loop;
            end if;
            if (RESET = '1') then
                s_frame_open <= '0';
            end if;
        end if;
    end process;

    -- =========================================================================
    --  1. STAGE: ACCUMULATOR AND OUTPUT WORD ASSEMBLY
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- FLUSH TIMEOUT
    -- -------------------------------------------------------------------------
    -- After FLUSH_TIMEOUT consecutive cycles without any new region, a
    -- non-empty accumulator is sent out as a partial word instead of waiting
    -- for regions that may never come.

    flush_cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_ce = '1') then
                if (s_dense_cnt_reg /= 0) then
                    s_flush_cnt <= (others => '0');
                elsif (s_flush_cnt < FLUSH_TIMEOUT) then
                    s_flush_cnt <= s_flush_cnt + 1;
                end if;
            end if;
            if (RESET = '1') then
                s_flush_cnt <= (others => '0');
            end if;
        end if;
    end process;

    s_flush_req <= '1' when (s_dense_cnt_reg = 0) and (s_flush_cnt >= FLUSH_TIMEOUT) else '0';

    -- -------------------------------------------------------------------------
    -- MERGE
    -- -------------------------------------------------------------------------
    -- The leftover regions followed by the newly compacted ones. Both lists
    -- are already dense, so this is a plain concatenation. Positions above
    -- s_merged_cnt carry no SOF and no EOF, which is what makes a partial word
    -- safe to send out as it is.

    merge_p : process (all)
        variable v_fill : natural range 0 to ACC_REGIONS;
    begin
        v_fill := to_integer(s_acc_fill);

        for m in 0 to MERGED_REGIONS-1 loop
            if (m < v_fill) then
                s_merged_data(m)    <= s_acc_data(m);
                s_merged_meta(m)    <= s_acc_meta(m);
                s_merged_sof_pos(m) <= s_acc_sof_pos(m);
                s_merged_eof_pos(m) <= s_acc_eof_pos(m);
                s_merged_sof(m)     <= s_acc_sof(m);
                s_merged_eof(m)     <= s_acc_eof(m);
            elsif (m-v_fill < REGIONS) then
                s_merged_data(m)    <= s_dense_data_reg(m-v_fill);
                s_merged_meta(m)    <= s_dense_meta_reg(m-v_fill);
                s_merged_sof_pos(m) <= s_dense_sof_pos_reg(m-v_fill);
                s_merged_eof_pos(m) <= s_dense_eof_pos_reg(m-v_fill);
                s_merged_sof(m)     <= s_dense_sof_reg(m-v_fill);
                s_merged_eof(m)     <= s_dense_eof_reg(m-v_fill);
            else
                s_merged_data(m)    <= (others => '0');
                s_merged_meta(m)    <= (others => '0');
                s_merged_sof_pos(m) <= (others => '0');
                s_merged_eof_pos(m) <= (others => '0');
                s_merged_sof(m)     <= '0';
                s_merged_eof(m)     <= '0';
            end if;
        end loop;
    end process;

    s_merged_cnt <= s_acc_fill + s_dense_cnt_reg;

    -- The merged list already holds a whole output word ...
    s_emit_word <= '1' when (s_merged_cnt >= REGIONS) else '0';
    -- ... or it does not, but the flush timeout fired on a non-empty one that
    -- ends at a frame boundary. Sending a partial word that ends inside an
    -- unfinished frame would make its padding read as that frame continuing,
    -- so those regions keep waiting for the rest of the frame instead.
    s_emit_part <= '1' when (s_emit_word = '0' and s_flush_req = '1' and s_merged_cnt > 0 and s_acc_open = '0') else '0';

    -- -------------------------------------------------------------------------
    -- OUTPUT REGISTER
    -- -------------------------------------------------------------------------

    output_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_ce = '1') then
                for r in 0 to REGIONS-1 loop
                    s_tx_data_arr(r)    <= s_merged_data(r);
                    s_tx_meta_arr(r)    <= s_merged_meta(r);
                    s_tx_sof_pos_arr(r) <= s_merged_sof_pos(r);
                    s_tx_eof_pos_arr(r) <= s_merged_eof_pos(r);
                    s_tx_sof(r)         <= s_merged_sof(r);
                    s_tx_eof(r)         <= s_merged_eof(r);
                end loop;
                s_tx_src_rdy <= s_emit_word or s_emit_part;
            end if;
            if (RESET = '1') then
                s_tx_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------
    -- ACCUMULATOR REGISTER
    -- -------------------------------------------------------------------------
    -- Carries over what was not sent: the regions above the emitted word, or
    -- the whole merged list when nothing is sent at all. A partial word takes
    -- everything, so it leaves nothing behind. Either way the carried-over
    -- regions end where the input word ended, so they inherit its frame state.

    acc_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_ce = '1') then
                if (s_emit_word = '1') then
                    for a in 0 to ACC_REGIONS-1 loop
                        s_acc_data(a)    <= s_merged_data(REGIONS+a);
                        s_acc_meta(a)    <= s_merged_meta(REGIONS+a);
                        s_acc_sof_pos(a) <= s_merged_sof_pos(REGIONS+a);
                        s_acc_eof_pos(a) <= s_merged_eof_pos(REGIONS+a);
                        s_acc_sof(a)     <= s_merged_sof(REGIONS+a);
                        s_acc_eof(a)     <= s_merged_eof(REGIONS+a);
                    end loop;
                    s_acc_fill <= s_merged_cnt - REGIONS;
                elsif (s_emit_part = '1') then
                    s_acc_fill <= (others => '0');
                else
                    for a in 0 to ACC_REGIONS-1 loop
                        s_acc_data(a)    <= s_merged_data(a);
                        s_acc_meta(a)    <= s_merged_meta(a);
                        s_acc_sof_pos(a) <= s_merged_sof_pos(a);
                        s_acc_eof_pos(a) <= s_merged_eof_pos(a);
                        s_acc_sof(a)     <= s_merged_sof(a);
                        s_acc_eof(a)     <= s_merged_eof(a);
                    end loop;
                    s_acc_fill <= s_merged_cnt;
                end if;
                s_acc_open <= s_frame_open;
            end if;
            if (RESET = '1') then
                s_acc_fill <= (others => '0');
                s_acc_open <= '0';
            end if;
        end if;
    end process;

    -- =========================================================================
    --  OUTPUT
    -- =========================================================================

    TX_DATA    <= slv_array_ser(s_tx_data_arr);
    TX_META    <= slv_array_ser(s_tx_meta_arr);
    TX_SOF_POS <= slv_array_ser(s_tx_sof_pos_arr);
    TX_EOF_POS <= slv_array_ser(s_tx_eof_pos_arr);
    TX_SOF     <= s_tx_sof;
    TX_EOF     <= s_tx_eof;
    TX_SRC_RDY <= s_tx_src_rdy;

end architecture;
