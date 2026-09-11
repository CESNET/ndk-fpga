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
        CNT_MAX    : integer := 64
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

    constant DATA_W    : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant META_W    : natural := MFB_REGIONS*MFB_META_WIDTH;
    constant SOF_POS_W : natural := MFB_REGIONS*max(1, log2(MFB_REGION_SIZE));
    constant EOF_POS_W : natural := MFB_REGIONS*log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE);

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

    dst_rdy_tx <= TX_MFB_DST_RDY;

    -- =========================================================================
    -- Input registers and packet-boundary tracking (per input)
    -- =========================================================================

    rx_inputs_g : for i in 0 to MERGER_INPUTS-1 generate

        in_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (dst_rdy_int(i) = '1') then
                    data_dly(i)    <= RX_MFB_DATA(i);
                    meta_dly(i)    <= RX_MFB_META(i);
                    sof_dly(i)     <= RX_MFB_SOF(i);
                    eof_dly(i)     <= RX_MFB_EOF(i);
                    sof_pos_dly(i) <= RX_MFB_SOF_POS(i);
                    eof_pos_dly(i) <= RX_MFB_EOF_POS(i);
                end if;
            end if;
        end process;

        in_src_rdy_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    src_rdy_dly(i) <= '0';
                elsif (dst_rdy_int(i) = '1') then
                    src_rdy_dly(i) <= RX_MFB_SRC_RDY(i);
                end if;
            end if;
        end process;

        -- Tracking of incomplete packets in the words accepted into the input register
        inc_pkt_g : for r in 0 to MFB_REGIONS-1 generate
            inc_pkt(i)(r+1) <= (RX_MFB_SOF(i)(r) and not RX_MFB_EOF(i)(r) and not inc_pkt(i)(r)) or
                               (RX_MFB_SOF(i)(r) and RX_MFB_EOF(i)(r) and inc_pkt(i)(r)) or
                               (not RX_MFB_SOF(i)(r) and not RX_MFB_EOF(i)(r) and inc_pkt(i)(r));
        end generate;

        inc_pkt_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    inc_pkt(i)(0) <= '0';
                elsif (RX_MFB_SRC_RDY(i) = '1' and dst_rdy_int(i) = '1') then
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

        dst_rdy_int(i) <= (dst_rdy_tx or not src_rdy_dly(i)) when (sel = i and do_mask_leave = '0') else
                          not src_rdy_dly(i)                 when (sel /= i) else
                          '0'; -- the word being sent with a masked SOF is held for the replay

        RX_MFB_DST_RDY(i) <= dst_rdy_int(i);

    end generate;

    -- =========================================================================
    -- Round-robin arbitration
    -- =========================================================================

    other_rdy_p : process (all)
        variable other_rdy_v : std_logic;
    begin
        other_rdy_v := '0';
        for j in 0 to MERGER_INPUTS-1 loop
            if (j /= sel and src_rdy_dly(j) = '1') then
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
            if (src_rdy_dly(idx_v) = '1') then
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

    -- Leave the selected input when another one is waiting for too long or when
    -- the selected one has no valid data (a switch costs nothing then).
    want_leave    <= other_rdy and (cnt_reached or not src_rdy_dly(sel));
    -- After the return to this input, its held word is sent again with only the SOF
    -- that was masked out before. The arbiter must not leave during that word.
    do_replay     <= sof_masked(sel);
    do_mask_leave <= want_leave and mask_cut(sel) and not do_replay;
    switch_now    <= dst_rdy_tx and not do_replay and want_leave and (can_cut(sel) or mask_cut(sel));

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

    src_rdy_tx <= src_rdy_dly(sel);

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
