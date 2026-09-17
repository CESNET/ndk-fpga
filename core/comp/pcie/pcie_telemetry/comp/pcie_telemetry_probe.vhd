-- pcie_telemetry_probe.vhd: Telemetry probe placed in a fast clock domain
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The PCIE_TELEMETRY_PROBE observes several MFB buses and several BRAKE signals
-- in one fast clock domain. It reports the measured event counts to a slow clock
-- domain. A BRAKE signal is active in every cycle in which one named reason
-- stopped the data flow.
--
-- The probe keeps one narrow counter per telemetry channel. Every DRAIN_PERIOD
-- cycles all counters are read out and cleared. Each read value is called
-- a delta. The deltas are sent one by one into an asynchronous FIFO. The deltas
-- are summed into wide counters in the slow clock domain, so this module needs
-- only narrow counters. A counter cannot overflow between two read-outs, so no
-- event is lost.
--
-- The path from the observed signals to the counters has three register stages:
-- registered inputs, computed increments and the counters. The read-out path
-- adds two more, the group register and the FIFO input register.
--
-- Channel numbering, which also gives the order of the counters in memory:
--
-- - ``0`` -- elapsed CLK cycles,
-- - ``1 + b*(6+REGIONS) + 0`` -- words transferred on bus ``b``,
-- - ``1 + b*(6+REGIONS) + 1`` -- cycles bus ``b`` was stalled by its consumer,
-- - ``1 + b*(6+REGIONS) + 2`` -- transactions (SOF) started on bus ``b``,
-- - ``1 + b*(6+REGIONS) + 3`` -- items transferred on the MVB bus that belongs
--   to bus ``b``. Where the headers are carried on a separate MVB bus, every
--   transaction has an item here. Only a transaction with payload also appears
--   on the MFB. Buses with no MVB leave this counter at zero.
-- - ``1 + b*(6+REGIONS) + 4`` -- cycles the MVB bus of bus ``b`` was stalled by
--   its consumer. The MVB has a handshake of its own, so it can be stalled while
--   the MFB of the same bus runs. Buses with no MVB leave this at zero.
-- - ``1 + b*(6+REGIONS) + 5`` -- MFB items transferred on bus ``b``. A region
--   that ends a frame counts the items up to RX_EOF_POS. Every other region of
--   an open frame counts all of its items.
-- - ``1 + b*(6+REGIONS) + 6 + r`` -- cycles region ``r`` of bus ``b`` carried data,
-- - ``1 + BUSES*(6+REGIONS) + k`` -- cycles the BRAKE signal ``k`` was active.
--
entity PCIE_TELEMETRY_PROBE is
    generic (
        -- Number of observed MFB buses.
        BUSES            : natural := 2;
        -- Number of MFB regions of each observed bus. Buses with fewer regions
        -- must have the unused SOF/EOF bits tied to zero.
        REGIONS          : natural := 2;
        -- Number of MFB items in one region of each observed bus. A region must
        -- hold a single block, so that a frame always starts at its first item.
        REGION_ITEMS     : i_array_t(BUSES-1 downto 0) := (others => 8);
        -- Width of one RX_EOF_POS field, the log2 of the largest REGION_ITEMS.
        EOF_POS_WIDTH    : natural := 3;
        -- The largest REGION_ITEMS of any observed bus. It sizes the counters.
        -- The port clause needs the value as a plain generic, because it cannot
        -- search the REGION_ITEMS array.
        REGION_ITEMS_MAX : natural := 8;
        -- Number of observed BRAKE signals.
        BRAKES           : natural := 2;
        -- Number of CLK cycles between two read-outs of the counters. It must
        -- be a power of two. It also sets the counter width CNT_WIDTH.
        DRAIN_PERIOD     : natural := 4096;
        -- FPGA device
        DEVICE           : string  := "AGILEX"
    );
    port (
        -- =====================================================================
        --  OBSERVED CLOCK DOMAIN
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- Start of frame of each region of each observed bus.
        RX_SOF     : in  std_logic_vector(BUSES*REGIONS-1 downto 0);
        -- End of frame of each region of each observed bus.
        RX_EOF     : in  std_logic_vector(BUSES*REGIONS-1 downto 0);
        -- Item of the region in which the frame ends, valid with RX_EOF. The
        -- fields keep the order of RX_EOF. Unused high bits stay at zero.
        RX_EOF_POS : in  std_logic_vector(BUSES*REGIONS*EOF_POS_WIDTH-1 downto 0) := (others => '0');
        RX_SRC_RDY : in  std_logic_vector(BUSES-1 downto 0);
        RX_DST_RDY : in  std_logic_vector(BUSES-1 downto 0);
        -- BRAKE signals. Each bit is active while the reason it reports blocks
        -- the data.
        RX_BRAKE   : in  std_logic_vector(max(1,BRAKES)-1 downto 0) := (others => '0');

        -- Valid items of the MVB bus that belongs to each observed MFB bus, and
        -- its handshake. Tie SRC_RDY low on buses that have no MVB.
        RX_MVB_VLD     : in  std_logic_vector(BUSES*REGIONS-1 downto 0) := (others => '0');
        RX_MVB_SRC_RDY : in  std_logic_vector(BUSES-1 downto 0) := (others => '0');
        RX_MVB_DST_RDY : in  std_logic_vector(BUSES-1 downto 0) := (others => '0');

        -- Active for one CLK cycle at the start of every read-out of the
        -- counters.
        DRAIN_TICK : out std_logic;

        -- =====================================================================
        --  REPORTING CLOCK DOMAIN
        -- =====================================================================
        MI_CLK     : in  std_logic;
        MI_RESET   : in  std_logic;

        -- Channel index of the reported delta.
        TX_INDEX   : out std_logic_vector(log2(1+BUSES*(6+REGIONS)+BRAKES)-1 downto 0);
        -- Number of events counted on the channel since the previous read-out.
        TX_DELTA   : out std_logic_vector(log2(DRAIN_PERIOD*max(1,REGIONS*REGION_ITEMS_MAX)+1)-1 downto 0);
        TX_VLD     : out std_logic;
        TX_RD      : in  std_logic;

        -- Every change of this level clears both flags below.
        MI_FLAG_CLR : in  std_logic := '0';
        -- Set when the FIFO was full and a delta was lost. Stays set until the
        -- level of MI_FLAG_CLR changes.
        TX_FIFO_OVF : out std_logic;
        -- Set when a read-out started before the previous one finished. Stays
        -- set until the level of MI_FLAG_CLR changes.
        TX_OVERRUN  : out std_logic
    );
end entity;

architecture FULL of PCIE_TELEMETRY_PROBE is

    -- The largest number of items one region of any observed bus holds.
    function max_items_f return natural is
        variable items_v : natural;
    begin
        items_v := 1;
        for b in 0 to BUSES-1 loop
            items_v := max(items_v,REGION_ITEMS(b));
        end loop;
        return items_v;
    end function;

    -- Number of channels measured per observed bus.
    constant BUS_CHANNELS : natural := 6 + REGIONS;
    constant CHANNELS     : natural := 1 + BUSES*BUS_CHANNELS + BRAKES;
    constant IDX_WIDTH    : natural := log2(CHANNELS);
    -- The largest increment of a single channel in a single cycle. The item
    -- channel grows the fastest, by a whole word of items.
    constant MAX_STEP     : natural := max(1,REGIONS*REGION_ITEMS_MAX);
    constant STEP_WIDTH   : natural := log2(MAX_STEP+1);
    constant CNT_WIDTH    : natural := log2(DRAIN_PERIOD*MAX_STEP+1);
    -- Channels are read out in groups. One element of every group is captured
    -- and cleared at once. The captured values are then sent out one per cycle.
    constant GROUP_SIZE   : natural := 8;
    constant GROUPS       : natural := div_roundup(CHANNELS,GROUP_SIZE);
    constant SLOT_WIDTH   : natural := log2(GROUP_SIZE);
    constant POS_WIDTH    : natural := log2(GROUPS+1);
    constant SWEEP_CYCLES : natural := GROUP_SIZE*(GROUPS+1);
    constant PERIOD_WIDTH : natural := log2(DRAIN_PERIOD);
    constant FIFO_WIDTH   : natural := IDX_WIDTH + CNT_WIDTH;

    signal sof_reg          : std_logic_vector(BUSES*REGIONS-1 downto 0);
    signal eof_reg          : std_logic_vector(BUSES*REGIONS-1 downto 0);
    signal eof_pos_reg      : std_logic_vector(BUSES*REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal src_rdy_reg      : std_logic_vector(BUSES-1 downto 0);
    signal dst_rdy_reg      : std_logic_vector(BUSES-1 downto 0);
    signal brake_reg        : std_logic_vector(max(1,BRAKES)-1 downto 0);

    signal bus_move         : std_logic_vector(BUSES-1 downto 0);
    signal bus_hold         : std_logic_vector(BUSES-1 downto 0);
    signal mvb_hold         : std_logic_vector(BUSES-1 downto 0);
    signal region_vld       : std_logic_vector(BUSES*REGIONS-1 downto 0);
    signal frame_open       : std_logic_vector(BUSES-1 downto 0);
    signal frame_open_reg   : std_logic_vector(BUSES-1 downto 0);
    signal sof_sum          : u_array_t(BUSES-1 downto 0)(STEP_WIDTH-1 downto 0);
    signal item_sum         : u_array_t(BUSES-1 downto 0)(STEP_WIDTH-1 downto 0);
    signal mvb_sum          : u_array_t(BUSES-1 downto 0)(STEP_WIDTH-1 downto 0);

    signal mvb_vld_reg      : std_logic_vector(BUSES*REGIONS-1 downto 0);
    signal mvb_move         : std_logic_vector(BUSES-1 downto 0);
    signal mvb_src_rdy_reg  : std_logic_vector(BUSES-1 downto 0);
    signal mvb_dst_rdy_reg  : std_logic_vector(BUSES-1 downto 0);

    signal step             : u_array_t(CHANNELS-1 downto 0)(STEP_WIDTH-1 downto 0);
    signal step_reg         : u_array_t(CHANNELS-1 downto 0)(STEP_WIDTH-1 downto 0);
    signal cnt              : u_array_t(GROUPS*GROUP_SIZE-1 downto 0)(CNT_WIDTH-1 downto 0);
    signal cnt_clr          : std_logic_vector(GROUPS*GROUP_SIZE-1 downto 0);

    signal period_cnt       : unsigned(PERIOD_WIDTH-1 downto 0);
    signal drain_tick_sig   : std_logic;
    signal sweep_run        : std_logic;
    signal slot_cnt         : unsigned(SLOT_WIDTH-1 downto 0);
    signal pos_cnt          : unsigned(POS_WIDTH-1 downto 0);
    signal slot_onehot      : std_logic_vector(GROUP_SIZE-1 downto 0);
    signal capture_en       : std_logic;
    signal grp_val          : u_array_t(GROUPS-1 downto 0)(CNT_WIDTH-1 downto 0);

    signal emit_grp         : natural range 0 to GROUPS-1;
    signal emit_idx         : unsigned(IDX_WIDTH-1 downto 0);
    signal emit_chan        : natural range 0 to GROUPS*GROUP_SIZE-1;
    signal emit_en          : std_logic;
    signal fifo_wr_data     : std_logic_vector(FIFO_WIDTH-1 downto 0);
    signal fifo_wr_en       : std_logic;
    signal fifo_wr_full     : std_logic;
    signal fifo_rd_data     : std_logic_vector(FIFO_WIDTH-1 downto 0);
    signal fifo_rd_empty    : std_logic;

    signal fifo_ovf_reg     : std_logic;
    signal overrun_reg      : std_logic;
    signal flag_clr_tgl     : std_logic;
    signal flag_clr_tgl_reg : std_logic;
    signal flag_clr         : std_logic;

    signal mi_reset_sync    : std_logic;
    signal probe_reset      : std_logic;

begin

    assert (2**PERIOD_WIDTH = DRAIN_PERIOD)
        report "PCIE_TELEMETRY_PROBE: Set DRAIN_PERIOD to a power of two."
        severity failure;

    assert (SWEEP_CYCLES < DRAIN_PERIOD)
        report "PCIE_TELEMETRY_PROBE: Raise DRAIN_PERIOD, one drain must finish before the next one starts."
        severity failure;

    -- =========================================================================
    --  0. RESET OF BOTH DOMAINS
    -- =========================================================================

    -- The output FIFO is full while either of its two resets is active. A delta
    -- produced in that time would be dropped and reported as a lost delta, even
    -- though the measurement had not started. The probe therefore stays idle
    -- until both domains are out of reset.
    mi_reset_sync_i : entity work.ASYNC_RESET
    generic map (
        TWO_REG => false
    )
    port map (
        CLK        => CLK,
        ASYNC_RST  => MI_RESET,
        OUT_RST(0) => mi_reset_sync
    );

    probe_reset <= RESET or mi_reset_sync;

    -- =========================================================================
    --  1. INPUT SAMPLING REGISTERS
    -- =========================================================================

    -- The observed signals are only sampled here. They are never driven back.
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            sof_reg         <= RX_SOF;
            eof_reg         <= RX_EOF;
            eof_pos_reg     <= RX_EOF_POS;
            src_rdy_reg     <= RX_SRC_RDY;
            dst_rdy_reg     <= RX_DST_RDY;
            brake_reg       <= RX_BRAKE;
            mvb_vld_reg     <= RX_MVB_VLD;
            mvb_src_rdy_reg <= RX_MVB_SRC_RDY;
            mvb_dst_rdy_reg <= RX_MVB_DST_RDY;
            if (probe_reset = '1') then
                src_rdy_reg <= (others => '0');
                dst_rdy_reg <= (others => '0');
                brake_reg   <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    --  2. EVENT DECODING
    -- =========================================================================

    assert (REGION_ITEMS_MAX = max_items_f)
        report "PCIE_TELEMETRY_PROBE: Set REGION_ITEMS_MAX to the largest value of REGION_ITEMS."
        severity failure;

    bus_move <= src_rdy_reg and dst_rdy_reg;
    bus_hold <= src_rdy_reg and not dst_rdy_reg;
    mvb_move <= mvb_src_rdy_reg and mvb_dst_rdy_reg;
    mvb_hold <= mvb_src_rdy_reg and not mvb_dst_rdy_reg;

    -- A region carries frame data when a frame is already open in front of it or
    -- when a frame starts right in it.
    process (all)
        variable frm_open_v : std_logic;
    begin
        for b in 0 to BUSES-1 loop
            frm_open_v := frame_open_reg(b);
            for r in 0 to REGIONS-1 loop
                region_vld(b*REGIONS+r) <= frm_open_v or sof_reg(b*REGIONS+r);
                frm_open_v              := (frm_open_v or sof_reg(b*REGIONS+r)) and not eof_reg(b*REGIONS+r);
            end loop;
            frame_open(b) <= frm_open_v;
        end loop;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            for b in 0 to BUSES-1 loop
                if (bus_move(b) = '1') then
                    frame_open_reg(b) <= frame_open(b);
                end if;
            end loop;
            if (probe_reset = '1') then
                frame_open_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- Items of one word. A region that ends a frame carries the items up to its
    -- EOF_POS. Every other region of an open frame carries all of its items.
    process (all)
        variable items_v   : unsigned(STEP_WIDTH-1 downto 0);
        variable eof_pos_v : unsigned(EOF_POS_WIDTH-1 downto 0);
    begin
        for b in 0 to BUSES-1 loop
            items_v := (others => '0');
            for r in 0 to REGIONS-1 loop
                eof_pos_v := unsigned(eof_pos_reg((b*REGIONS+r+1)*EOF_POS_WIDTH-1 downto (b*REGIONS+r)*EOF_POS_WIDTH));
                if (region_vld(b*REGIONS+r) = '1') then
                    if (eof_reg(b*REGIONS+r) = '1') then
                        items_v := items_v + resize(eof_pos_v,STEP_WIDTH) + 1;
                    else
                        items_v := items_v + to_unsigned(REGION_ITEMS(b),STEP_WIDTH);
                    end if;
                end if;
            end loop;
            item_sum(b) <= items_v;
        end loop;
    end process;

    -- Every SOF of the cycle starts one transaction. A bus can start one
    -- transaction per region.
    process (all)
        variable sof_sum_v : unsigned(STEP_WIDTH-1 downto 0);
    begin
        for b in 0 to BUSES-1 loop
            sof_sum_v := (others => '0');
            for r in 0 to REGIONS-1 loop
                if (sof_reg(b*REGIONS+r) = '1') then
                    sof_sum_v := sof_sum_v + 1;
                end if;
            end loop;
            sof_sum(b) <= sof_sum_v;
        end loop;
    end process;

    process (all)
        variable mvb_sum_v : unsigned(STEP_WIDTH-1 downto 0);
    begin
        for b in 0 to BUSES-1 loop
            mvb_sum_v := (others => '0');
            for r in 0 to REGIONS-1 loop
                if (mvb_vld_reg(b*REGIONS+r) = '1') then
                    mvb_sum_v := mvb_sum_v + 1;
                end if;
            end loop;
            mvb_sum(b) <= mvb_sum_v;
        end loop;
    end process;

    step(0) <= to_unsigned(1,STEP_WIDTH);

    bus_step_g : for b in 0 to BUSES-1 generate
        step(1+b*BUS_CHANNELS+0) <= to_unsigned(1,STEP_WIDTH) when (bus_move(b) = '1') else (others => '0');
        step(1+b*BUS_CHANNELS+1) <= to_unsigned(1,STEP_WIDTH) when (bus_hold(b) = '1') else (others => '0');
        step(1+b*BUS_CHANNELS+2) <= sof_sum(b) when (bus_move(b) = '1') else (others => '0');
        step(1+b*BUS_CHANNELS+3) <= mvb_sum(b) when (mvb_move(b) = '1') else (others => '0');
        step(1+b*BUS_CHANNELS+4) <= to_unsigned(1,STEP_WIDTH) when (mvb_hold(b) = '1') else (others => '0');
        step(1+b*BUS_CHANNELS+5) <= item_sum(b) when (bus_move(b) = '1') else (others => '0');

        region_step_g : for r in 0 to REGIONS-1 generate
            step(1+b*BUS_CHANNELS+6+r) <= to_unsigned(1,STEP_WIDTH)
                when (bus_move(b) = '1' and region_vld(b*REGIONS+r) = '1') else
 (others => '0');
        end generate;
    end generate;

    brake_step_g : for k in 0 to BRAKES-1 generate
        step(1+BUSES*BUS_CHANNELS+k) <= to_unsigned(1,STEP_WIDTH) when (brake_reg(k) = '1') else (others => '0');
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            step_reg <= step;
            if (probe_reset = '1') then
                step_reg <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -- =========================================================================
    --  3. CHANNEL COUNTERS
    -- =========================================================================

    -- Counters of the padding channels are never read out. The synthesis tool
    -- removes them.
    cnt_g : for i in 0 to GROUPS*GROUP_SIZE-1 generate
        used_cnt_g : if (i < CHANNELS) generate
            cnt_clr(i) <= capture_en and slot_onehot(i mod GROUP_SIZE);

            -- The clear keeps the increment of the current cycle. No event is lost.
            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (probe_reset = '1') then
                        cnt(i) <= (others => '0');
                    elsif (cnt_clr(i) = '1') then
                        cnt(i) <= resize(step_reg(i),CNT_WIDTH);
                    else
                        cnt(i) <= cnt(i) + step_reg(i);
                    end if;
                end if;
            end process;
        else generate
            cnt_clr(i) <= '0';
            cnt(i)     <= (others => '0');
        end generate;
    end generate;

    -- =========================================================================
    --  4. DRAIN SWEEP
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            period_cnt <= period_cnt + 1;
            if (probe_reset = '1') then
                period_cnt <= (others => '0');
            end if;
        end if;
    end process;

    drain_tick_sig <= '1' when (period_cnt = (2**PERIOD_WIDTH-1)) else '0';
    DRAIN_TICK     <= drain_tick_sig;

    -- The sweep walks all slots of all groups. Position 0 of every slot captures
    -- one element of each group. The remaining positions send those values out.
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (drain_tick_sig = '1') then
                sweep_run <= '1';
                slot_cnt  <= (others => '0');
                pos_cnt   <= (others => '0');
            elsif (sweep_run = '1') then
                if (pos_cnt = GROUPS) then
                    pos_cnt <= (others => '0');
                    if (slot_cnt = GROUP_SIZE-1) then
                        sweep_run <= '0';
                    else
                        slot_cnt <= slot_cnt + 1;
                    end if;
                else
                    pos_cnt <= pos_cnt + 1;
                end if;
            end if;

            if (probe_reset = '1') then
                sweep_run <= '0';
                slot_cnt  <= (others => '0');
                pos_cnt   <= (others => '0');
            end if;
        end if;
    end process;

    capture_en <= '1' when (sweep_run = '1' and pos_cnt = 0) else '0';

    slot_onehot_p : process (all)
    begin
        slot_onehot                          <= (others => '0');
        slot_onehot(to_integer(slot_cnt))    <= '1';
    end process;

    grp_g : for g in 0 to GROUPS-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (capture_en = '1') then
                    grp_val(g) <= cnt(g*GROUP_SIZE + to_integer(slot_cnt));
                end if;
            end if;
        end process;
    end generate;

    -- =========================================================================
    --  5. DELTA OUTPUT
    -- =========================================================================

    -- Position 0 of every slot captures the group registers. Positions 1 to
    -- GROUPS send out the captured value of group pos_cnt-1.
    emit_grp  <= work.math_pack.min(max(to_integer(pos_cnt),1),GROUPS)-1;
    emit_chan <= emit_grp*GROUP_SIZE + to_integer(slot_cnt);
    emit_idx  <= to_unsigned(emit_chan mod 2**IDX_WIDTH, IDX_WIDTH);
    emit_en   <= '1' when (sweep_run = '1' and pos_cnt /= 0 and emit_chan < CHANNELS) else '0';

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            fifo_wr_data <= std_logic_vector(emit_idx) & std_logic_vector(grp_val(emit_grp));
            fifo_wr_en   <= emit_en;

            if (flag_clr = '1') then
                fifo_ovf_reg <= '0';
                overrun_reg  <= '0';
            end if;
            if (fifo_wr_en = '1' and fifo_wr_full = '1') then
                fifo_ovf_reg <= '1';
            end if;
            if (drain_tick_sig = '1' and sweep_run = '1') then
                overrun_reg <= '1';
            end if;

            if (probe_reset = '1') then
                fifo_wr_en   <= '0';
                fifo_ovf_reg <= '0';
                overrun_reg  <= '0';
            end if;
        end if;
    end process;

    fifo_i : entity work.ASFIFOX
    generic map (
        DATA_WIDTH => FIFO_WIDTH,
        ITEMS      => 2**log2(2*GROUPS*GROUP_SIZE),
        RAM_TYPE   => "LUT",
        FWFT_MODE  => True,
        OUTPUT_REG => True,
        DEVICE     => DEVICE
    )
    port map (
        WR_CLK    => CLK,
        WR_RST    => probe_reset,
        WR_DATA   => fifo_wr_data,
        WR_EN     => fifo_wr_en,
        WR_FULL   => fifo_wr_full,
        WR_AFULL  => open,
        WR_STATUS => open,

        RD_CLK    => MI_CLK,
        RD_RST    => MI_RESET,
        RD_DATA   => fifo_rd_data,
        RD_EN     => TX_RD,
        RD_EMPTY  => fifo_rd_empty,
        RD_AEMPTY => open,
        RD_STATUS => open
    );

    TX_INDEX <= fifo_rd_data(FIFO_WIDTH-1 downto CNT_WIDTH);
    TX_DELTA <= fifo_rd_data(CNT_WIDTH-1 downto 0);
    TX_VLD   <= not fifo_rd_empty;

    -- The clear request crosses as a level change. Every edge clears the flags.
    flag_clr_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG  => false,
        TWO_REG => true
    )
    port map (
        ACLK     => MI_CLK,
        ARST     => MI_RESET,
        ADATAIN  => MI_FLAG_CLR,
        BCLK     => CLK,
        BRST     => probe_reset,
        BDATAOUT => flag_clr_tgl
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            flag_clr_tgl_reg <= flag_clr_tgl;
            if (probe_reset = '1') then
                flag_clr_tgl_reg <= '0';
            end if;
        end if;
    end process;

    flag_clr <= flag_clr_tgl xor flag_clr_tgl_reg;

    ovf_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG  => false,
        TWO_REG => true
    )
    port map (
        ACLK     => CLK,
        ARST     => probe_reset,
        ADATAIN  => fifo_ovf_reg,
        BCLK     => MI_CLK,
        BRST     => MI_RESET,
        BDATAOUT => TX_FIFO_OVF
    );

    overrun_sync_i : entity work.ASYNC_OPEN_LOOP
    generic map (
        IN_REG  => false,
        TWO_REG => true
    )
    port map (
        ACLK     => CLK,
        ARST     => probe_reset,
        ADATAIN  => overrun_reg,
        BCLK     => MI_CLK,
        BRST     => MI_RESET,
        BDATAOUT => TX_OVERRUN
    );

end architecture;
