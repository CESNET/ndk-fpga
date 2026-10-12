-- mfb_merger_simple_gen.vhd: This component is merges multiple input MFB interfaces to one.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Vladislav Valek <valekv@cesnet.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

-- This is a generic implementation of the MFB Merger when the number of input interfaces can
-- be set to arbitrary large number.
--
-- The Merger holds one prefetched word per input and switches the words of the selected
-- input to the output with a single round-robin arbiter, a single multiplexer and one
-- output register (latency is 2 clock cycles, independent of MERGER_INPUTS).
-- The selected input can change only on a packet boundary (or with the help of masking,
-- see the MASKING_EN generic). The Merger tries to switch to the next input (in the
-- round-robin order) when:
--
-- * the selected input has had data for CNT_MAX clock cycles while another input
--   was waiting (prevents starvation), or
-- * the selected input has no valid data (and another input does).
--
-- With IN_FIFO_DEPTH > 0, each input has an MFB_FIFOX in front of the input register.
-- With STORED_EOF_EN, the Merger starts a packet only when the EOF of this packet
-- is already in the input FIFO. A started packet then needs no data that are not stored yet.
-- The selected input can wait for such an EOF while another input has data. Then
-- the Merger sends the end of the current packet with the next SOF masked and switches.
--
entity MFB_MERGER_SIMPLE_GEN is
    generic (
        -- number of independent input MFB interfaces, any positive number
        MERGER_INPUTS : natural := 2;

        -- MFB parameters
        MFB_REGIONS     : natural := 2;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;
        MFB_META_WIDTH  : natural := 8;

        -- Enable masking SOF and EOF due to switch to the other input.
        MASKING_EN : boolean := TRUE;
        -- Maximum amount of clock periods with destination ready before it tries to switch to the other input.
        CNT_MAX    : integer := 64;

        -- Depth of the optional MFB_FIFOX on each input in words. 0 disables the FIFOs.
        IN_FIFO_DEPTH : natural := 0;
        -- Start a packet only when its EOF is already in the input FIFO.
        -- Requires IN_FIFO_DEPTH > 0 and MASKING_EN = True.
        STORED_EOF_EN : boolean := False;
        -- Maximum size of a packet in MFB items. With STORED_EOF_EN, each input
        -- FIFO must hold a packet of this size.
        PKT_SIZE_MAX  : natural := 2**14;
        -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE        : string  := "AGILEX"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK : in std_logic;
        RST : in std_logic;

        -- =====================================================================
        -- Multiple input RX MFB interfaces
        -- =====================================================================
        RX_MFB_DATA    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t(MERGER_INPUTS -1 downto 0)(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS -1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS -1 downto 0);

        -- =====================================================================
        -- Single output TX interface
        -- =====================================================================
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER_SIMPLE_GEN is

    constant DATA_W        : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant META_W        : natural := MFB_REGIONS*MFB_META_WIDTH;
    constant SOF_POS_W     : natural := MFB_REGIONS*max(1, log2(MFB_REGION_SIZE));
    constant EOF_POS_W     : natural := MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE);
    constant INC_W         : natural := log2(MFB_REGIONS+1);
    -- The counter is signed, because the registered increment can come later
    -- than the word with the same EOF leaves the FIFO.
    constant STORED_W      : natural := max(log2(IN_FIFO_DEPTH*MFB_REGIONS+1), INC_W) + 2;
    -- A packet can start at the last Block of a word.
    constant WORD_ITEMS    : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    constant PKT_WORDS_MAX : natural := div_roundup(PKT_SIZE_MAX + WORD_ITEMS - MFB_BLOCK_SIZE, WORD_ITEMS);

    -- Outputs of the input FIFOs
    signal fi_data    : slv_array_t(MERGER_INPUTS-1 downto 0)(DATA_W-1 downto 0);
    signal fi_meta    : slv_array_t(MERGER_INPUTS-1 downto 0)(META_W-1 downto 0);
    signal fi_sof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fi_eof     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fi_sof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(SOF_POS_W-1 downto 0);
    signal fi_eof_pos : slv_array_t(MERGER_INPUTS-1 downto 0)(EOF_POS_W-1 downto 0);
    signal fi_src_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal rx_dst_rdy : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Input word registers (one prefetched word per input)
    signal data_dly    : slv_array_t(MERGER_INPUTS-1 downto 0)(DATA_W-1 downto 0);
    signal meta_dly    : slv_array_t(MERGER_INPUTS-1 downto 0)(META_W-1 downto 0);
    signal sof_dly     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal eof_dly     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal sof_pos_dly : slv_array_t(MERGER_INPUTS-1 downto 0)(SOF_POS_W-1 downto 0);
    signal eof_pos_dly : slv_array_t(MERGER_INPUTS-1 downto 0)(EOF_POS_W-1 downto 0);
    signal src_rdy_dly : std_logic_vector(MERGER_INPUTS-1 downto 0);
    signal dst_rdy_int : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Incomplete-packet tracking per input. Index 0 is a register: '1' means that
    -- the word currently held in the input register leaves a packet open (the
    -- packet continues in the following words).
    signal inc_pkt     : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS downto 0);
    signal eof_any_dly : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- The stream can be cut right after the held word (clean packet boundary).
    signal can_cut     : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- The held word ends with the start of an unfinished packet, which can be
    -- masked out to create a packet boundary (the rest of the word ends with EOF).
    signal mask_cut    : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- One-hot position of the last (highest) SOF in the held word.
    signal sof_last_oh : slv_array_t(MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    -- The held word was already sent with its last SOF masked; on return to this
    -- input it must be sent again with only that SOF (start of the masked packet).
    signal sof_masked  : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Counters of EOFs that are in each input FIFO
    signal stored_inc_reg : u_array_t(MERGER_INPUTS-1 downto 0)(INC_W-1 downto 0);
    signal stored_cnt     : s_array_t(MERGER_INPUTS-1 downto 0)(STORED_W-1 downto 0);
    -- The EOF of the packet that stays open after the held word is in the input FIFO.
    signal pkt_stored     : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- The held word starts a packet whose EOF is not stored yet.
    signal wait_pkt       : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- Only the SOF of the waiting packet is left to send from the held word.
    signal only_open      : std_logic_vector(MERGER_INPUTS-1 downto 0);
    -- The held word contains data that can be sent now.
    signal vld            : std_logic_vector(MERGER_INPUTS-1 downto 0);

    -- Arbitration
    signal sel           : natural range 0 to MERGER_INPUTS-1;
    signal rr_next       : natural range 0 to MERGER_INPUTS-1;
    signal other_rdy     : std_logic;
    signal cnt           : unsigned(max(1, log2(CNT_MAX))-1 downto 0);
    signal cnt_reached   : std_logic;
    signal want_leave    : std_logic;
    signal do_replay     : std_logic;
    signal do_mask_leave : std_logic;
    signal switch_now    : std_logic;

    -- Output signals
    signal sof_tx     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal eof_tx     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal src_rdy_tx : std_logic;
    signal dst_rdy_tx : std_logic;

begin

    assert (not STORED_EOF_EN or (MASKING_EN and IN_FIFO_DEPTH > 0))
        report "MFB_MERGER_SIMPLE_GEN: Set MASKING_EN = True and IN_FIFO_DEPTH > 0 when STORED_EOF_EN = True."
        severity failure;

    -- A full FIFO must contain an EOF, so that the Merger can start a packet from it.
    assert (not STORED_EOF_EN or IN_FIFO_DEPTH >= PKT_WORDS_MAX)
        report "MFB_MERGER_SIMPLE_GEN: Set IN_FIFO_DEPTH to at least " & integer'image(PKT_WORDS_MAX) & " words to hold a packet of PKT_SIZE_MAX items."
        severity failure;

    dst_rdy_tx <= TX_MFB_DST_RDY;

    -- =========================================================================
    -- Input registers and packet-boundary tracking (per input)
    -- =========================================================================

    rx_inputs_g : for i in 0 to MERGER_INPUTS-1 generate

        in_fifo_g : if IN_FIFO_DEPTH > 0 generate
            in_fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REGION_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                META_WIDTH  => MFB_META_WIDTH,
                FIFO_DEPTH  => IN_FIFO_DEPTH,
                RAM_TYPE    => "AUTO",
                DEVICE      => DEVICE
            )
            port map (
                CLK         => CLK,
                RST         => RST,

                RX_DATA     => RX_MFB_DATA(i),
                RX_META     => RX_MFB_META(i),
                RX_SOF_POS  => RX_MFB_SOF_POS(i),
                RX_EOF_POS  => RX_MFB_EOF_POS(i),
                RX_SOF      => RX_MFB_SOF(i),
                RX_EOF      => RX_MFB_EOF(i),
                RX_SRC_RDY  => RX_MFB_SRC_RDY(i),
                RX_DST_RDY  => rx_dst_rdy(i),

                TX_DATA     => fi_data(i),
                TX_META     => fi_meta(i),
                TX_SOF_POS  => fi_sof_pos(i),
                TX_EOF_POS  => fi_eof_pos(i),
                TX_SOF      => fi_sof(i),
                TX_EOF      => fi_eof(i),
                TX_SRC_RDY  => fi_src_rdy(i),
                TX_DST_RDY  => dst_rdy_int(i),

                FIFO_STATUS => open,
                FIFO_AFULL  => open,
                FIFO_AEMPTY => open
            );
        else generate
            fi_data(i)    <= RX_MFB_DATA(i);
            fi_meta(i)    <= RX_MFB_META(i);
            fi_sof(i)     <= RX_MFB_SOF(i);
            fi_eof(i)     <= RX_MFB_EOF(i);
            fi_sof_pos(i) <= RX_MFB_SOF_POS(i);
            fi_eof_pos(i) <= RX_MFB_EOF_POS(i);
            fi_src_rdy(i) <= RX_MFB_SRC_RDY(i);
            rx_dst_rdy(i) <= dst_rdy_int(i);
        end generate;

        RX_MFB_DST_RDY(i) <= rx_dst_rdy(i);

        in_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (dst_rdy_int(i) = '1') then
                    data_dly(i)    <= fi_data(i);
                    meta_dly(i)    <= fi_meta(i);
                    sof_dly(i)     <= fi_sof(i);
                    eof_dly(i)     <= fi_eof(i);
                    sof_pos_dly(i) <= fi_sof_pos(i);
                    eof_pos_dly(i) <= fi_eof_pos(i);
                end if;
            end if;
        end process;

        in_src_rdy_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    src_rdy_dly(i) <= '0';
                elsif (dst_rdy_int(i) = '1') then
                    src_rdy_dly(i) <= fi_src_rdy(i);
                end if;
            end if;
        end process;

        -- Tracking of incomplete packets in the words accepted into the input register
        inc_pkt_g : for r in 0 to MFB_REGIONS-1 generate
            inc_pkt(i)(r+1) <= (fi_sof(i)(r) and not fi_eof(i)(r) and not inc_pkt(i)(r)) or
                               (fi_sof(i)(r) and fi_eof(i)(r) and inc_pkt(i)(r)) or
                               (not fi_sof(i)(r) and not fi_eof(i)(r) and inc_pkt(i)(r));
        end generate;

        inc_pkt_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    inc_pkt(i)(0) <= '0';
                elsif (fi_src_rdy(i) = '1' and dst_rdy_int(i) = '1') then
                    inc_pkt(i)(0) <= inc_pkt(i)(MFB_REGIONS);
                end if;
            end if;
        end process;

        eof_any_dly(i) <= or (eof_dly(i));

        can_cut(i) <= (not inc_pkt(i)(0)) and (eof_any_dly(i) or not src_rdy_dly(i));

        -- A word with an EOF that leaves a packet open must contain the SOF of that
        -- packet (after its last EOF), so the SOF can be masked to create a boundary.
        mask_cut(i) <= inc_pkt(i)(0) and eof_any_dly(i) and src_rdy_dly(i) when MASKING_EN else '0';

        sof_last_oh_p : process (all)
        begin
            sof_last_oh(i) <= (others => '0');
            for r in MFB_REGIONS-1 downto 0 loop
                if (sof_dly(i)(r) = '1') then
                    sof_last_oh(i)(r) <= '1';
                    exit;
                end if;
            end loop;
        end process;

        -- ---------------------------------------------------------------------
        -- Counter of EOFs in the input FIFO
        -- ---------------------------------------------------------------------
        stored_eof_g : if STORED_EOF_EN generate
            -- Both values of the counter are computed in advance. The handshake
            -- (dst_rdy_int) only selects one of them.
            stored_cnt_p : process (CLK)
                variable cnt_inc_v : signed(STORED_W-1 downto 0);
                variable cnt_dec_v : signed(STORED_W-1 downto 0);
            begin
                if (rising_edge(CLK)) then
                    cnt_inc_v         := stored_cnt(i) + signed(resize(stored_inc_reg(i), STORED_W));
                    cnt_dec_v         := cnt_inc_v - count_ones(fi_eof(i));
                    if (RX_MFB_SRC_RDY(i) = '1' and rx_dst_rdy(i) = '1') then
                        stored_inc_reg(i) <= to_unsigned(count_ones(RX_MFB_EOF(i)), INC_W);
                    else
                        stored_inc_reg(i) <= (others => '0');
                    end if;
                    if (fi_src_rdy(i) = '1' and dst_rdy_int(i) = '1') then
                        stored_cnt(i) <= cnt_dec_v;
                        pkt_stored(i) <= tsel(cnt_dec_v > 0, '1', '0');
                    else
                        stored_cnt(i) <= cnt_inc_v;
                        pkt_stored(i) <= tsel(cnt_inc_v > 0, '1', '0');
                    end if;
                    if (RST = '1') then
                        stored_inc_reg(i) <= (others => '0');
                        stored_cnt(i)     <= (others => '0');
                        pkt_stored(i)     <= '0';
                    end if;
                end if;
            end process;
        else generate
            pkt_stored(i) <= '1';
        end generate;

        wait_pkt(i)  <= src_rdy_dly(i) and inc_pkt(i)(0) and (or sof_dly(i)) and not pkt_stored(i);
        only_open(i) <= wait_pkt(i) and (sof_masked(i) or not eof_any_dly(i));
        vld(i)       <= src_rdy_dly(i) and not only_open(i);

        dst_rdy_int(i) <= (dst_rdy_tx or not src_rdy_dly(i)) when (sel = i and do_mask_leave = '0' and wait_pkt(i) = '0') else
                          not src_rdy_dly(i)                 when (sel /= i) else
                          '0'; -- the word is held for the replay of its masked SOF or until the EOF is stored

    end generate;

    -- =========================================================================
    -- Round-robin arbitration
    -- =========================================================================

    other_rdy_p : process (all)
        variable other_rdy_v : std_logic;
    begin
        other_rdy_v := '0';
        for j in 0 to MERGER_INPUTS-1 loop
            if (j /= sel and vld(j) = '1') then
                other_rdy_v := '1';
            end if;
        end loop;
        other_rdy <= other_rdy_v;
    end process;

    -- The nearest following input (in the round-robin order) with a valid word
    rr_next_p : process (all)
        variable idx_v     : natural range 0 to 2*MERGER_INPUTS-2;
        variable rr_next_v : natural range 0 to MERGER_INPUTS-1;
    begin
        rr_next_v := sel;
        for k in MERGER_INPUTS-1 downto 1 loop
            -- wrap of (sel + k) to the input range
            idx_v := sel + k;
            if (idx_v >= MERGER_INPUTS) then
                idx_v := idx_v - MERGER_INPUTS;
            end if;
            if (vld(idx_v) = '1') then
                rr_next_v := idx_v;
            end if;
        end loop;
        rr_next <= rr_next_v;
    end process;

    cnt_reached <= '0' when (cnt < CNT_MAX-1) else '1';

    -- Counts cycles for which the output is ready while another input is waiting
    cnt_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if ((RST = '1') or (switch_now = '1') or (other_rdy = '0')) then
                cnt <= (others => '0');
            elsif ((dst_rdy_tx = '1') and (cnt_reached = '0')) then
                cnt <= cnt + 1;
            end if;
        end if;
    end process;

    -- Leave the selected input when another one is waiting for too long, when
    -- the selected one has no valid data (a switch costs nothing then), or when
    -- the selected one waits for a stored EOF.
    want_leave    <= other_rdy and (cnt_reached or not vld(sel) or wait_pkt(sel));
    -- After the return to this input, its held word is sent again with only the SOF
    -- that was masked out before. The arbiter must not leave during that word.
    do_replay     <= sof_masked(sel) and not wait_pkt(sel);
    do_mask_leave <= want_leave and mask_cut(sel) and not sof_masked(sel);
    switch_now    <= dst_rdy_tx and not do_replay and want_leave and (can_cut(sel) or mask_cut(sel) or only_open(sel));

    arbiter_state_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (dst_rdy_tx = '1') then
                if (do_replay = '1') then
                    sof_masked(sel) <= '0';
                elsif (do_mask_leave = '1') then
                    sof_masked(sel) <= '1';
                end if;
                if (switch_now = '1') then
                    sel <= rr_next;
                end if;
            end if;
            if (RST = '1') then
                sel        <= 0;
                sof_masked <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Output multiplexer with SOF/EOF masking
    -- =========================================================================

    sof_tx <= sof_last_oh(sel)                        when (do_replay = '1')     else
              (sof_dly(sel) and not sof_last_oh(sel)) when (do_mask_leave = '1') else
              sof_dly(sel);

    eof_tx <= (others => '0') when (do_replay = '1') else eof_dly(sel);

    -- While the selected input waits for a stored EOF, only the part of the held
    -- word before the masked SOF is sent.
    src_rdy_tx <= src_rdy_dly(sel) and (not wait_pkt(sel) or do_mask_leave);

    reg_out_data_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (dst_rdy_tx = '1') then
                TX_MFB_DATA    <= data_dly(sel);
                TX_MFB_META    <= meta_dly(sel);
                TX_MFB_SOF     <= sof_tx;
                TX_MFB_EOF     <= eof_tx;
                TX_MFB_SOF_POS <= sof_pos_dly(sel);
                TX_MFB_EOF_POS <= eof_pos_dly(sel);
            end if;
        end if;
    end process;

    reg_out_src_rdy_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                TX_MFB_SRC_RDY <= '0';
            elsif (dst_rdy_tx = '1') then
                TX_MFB_SRC_RDY <= src_rdy_tx;
            end if;
        end if;
    end process;

end architecture;
