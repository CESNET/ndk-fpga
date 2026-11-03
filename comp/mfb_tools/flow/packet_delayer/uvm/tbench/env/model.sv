// model.sv: Retiming reference model of the MFB_PACKET_DELAYER
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause
//
// Time-aware reference: predicts the simulation time at which the DUT is
// expected to release each packet, derived ONLY from the packet timestamp and
// the fixed structural constants (never from a DUT signal), then emits
// delayer_data_item / delayer_meta_item carrying expected_release.
//
// One timestamp unit = one clock period = TICK = CLK_PERIOD.
//
// Release time (t_mon = time the TX monitor observes the packet):
//   t_mon[0] = max(t_rst + ts[0]*TICK + Q, t_arr[0] + A + Q)
//   TS_FORMAT = 1: t_mon[i] = max(t_mon[0] + ts[i]*TICK, t_mon[i-1] + HOL, t_arr[i] + A + Q)
//   TS_FORMAT = 0: t_mon[i] = max(t_prev + ts[i]*TICK, t_arr[i] + A + Q)
// where t_rst = RESET release time (reset agent sync), t_arr = RX SOF monitor stamp,
//   Q = PIPE_LAT, A = ARRIV_LAT, HOL = max(words_prev - share_prev, 1) + GAP_TIME.
//
// The DUT reads SOFs strictly in order (a region whose timestamp has not yet
// elapsed blocks all following regions of the same MFB word), so packets are
// released in arrival order for both formats. The model therefore handles one
// packet at a time; for TS_FORMAT = 0 each packet chains from the previously
// released one.
//
// A frame spans one or two MFB words; the model uses boolean tests on the RX
// stamps: words = (t_eof_rx > t_sof_rx) ? 2 : 1 and
// share_prev = (t_sof_rx <= t_eof_rx_prev). The data monitor stamps the EOF,
// the meta monitor stamps the SOF, so t_data = t_mon + words_span, t_meta = t_mon.

// Counts TIME_RESET assertions reported by the TIME_RESET (uvm_reset) agent
class time_reset_sync extends uvm_reset::sync;
    int unsigned count = 0;

    virtual function void reset_start(time start_time);
        count++;
    endfunction
endclass

class model #(
    int unsigned ITEM_WIDTH,
    int unsigned META_WIDTH,
    int unsigned EXTENDED_META_WIDTH,
    int unsigned TS_WIDTH,
    int unsigned TS_FORMAT,
    time         CLK_PERIOD,
    int unsigned PIPE_LAT,
    int unsigned ARRIV_LAT,
    int unsigned GAP_TIME
) extends uvm_component;
    `uvm_component_param_utils(uvm_packet_delayer::model#(
        ITEM_WIDTH, META_WIDTH, EXTENDED_META_WIDTH, TS_WIDTH, TS_FORMAT,
        CLK_PERIOD, PIPE_LAT, ARRIV_LAT, GAP_TIME))

    // One timestamp unit = one clock period (CURRENT_TIME increments by 1 per clock)
    localparam time TICK = CLK_PERIOD;

    uvm_tlm_analysis_fifo #(uvm_logic_vector_array::sequence_item #(ITEM_WIDTH))     data_in;
    uvm_tlm_analysis_fifo #(uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH))  meta_in;
    uvm_analysis_port #(uvm_packet_delayer::delayer_data_item #(ITEM_WIDTH))         data_out;
    uvm_analysis_port #(uvm_packet_delayer::delayer_meta_item #(META_WIDTH))         meta_out;

    // Reset release time (time anchor) and TIME_RESET assertions, connected to
    // the reset agents by the env
    uvm_reset::sync_terminate reset_sync;
    time_reset_sync           time_reset_sync_i;

    // TIME_RESET support: each observed pulse re-arms the DUT epoch, which the
    // DUT applies with the next SOF. reanchor_pending holds the request until
    // the next packet builds the new reference point. TIME_RESET only affects
    // the DUT for TS_FORMAT = 1 (absolute timestamps); for TS_FORMAT = 0 the
    // DUT ignores it, so the model must ignore it too.
    bit          reanchor_pending = 0;
    int unsigned n_time_reset     = 0;
    int unsigned m_n_pkts         = 0;

    function new(string name = "model", uvm_component parent = null);
        super.new(name, parent);

        data_in       = new("data_in",       this);
        data_out      = new("data_out",      this);

        meta_in       = new("meta_in",       this);
        meta_out      = new("meta_out",      this);

        reset_sync        = new();
        time_reset_sync_i = new();
    endfunction

    function int unsigned used();
        int unsigned ret = 0;
        ret |= (data_in.used() != 0);
        ret |= (meta_in.used() != 0);
        return ret;
    endfunction

    // Number of observed TIME_RESET assertions
    function int unsigned time_reset_count();
        return n_time_reset;
    endfunction

    // Number of packets consumed from the RX monitors so far. Used by the test
    // to know whether every generated packet has actually reached the model
    // (avoids a drain race where the scoreboard looks empty while the last
    // packet is still in flight).
    function int unsigned received_count();
        return m_n_pkts;
    endfunction

    // Max of two/three time values
    function automatic time tmax2(time a, time b);
        return (a > b) ? a : b;
    endfunction

    function automatic time tmax3(time a, time b, time c);
        time r = a;
        if (b > r) begin
            r = b;
        end
        if (c > r) begin
            r = c;
        end
        return r;
    endfunction

    // Consume TIME_RESET assertions observed since the previous packet. Each
    // pulse re-arms the DUT epoch; the re-anchor is applied to THIS packet (the
    // next SOF after the pulse). Only TS_FORMAT = 1 reacts (matches the DUT).
    task consume_time_reset();
        while (n_time_reset < time_reset_sync_i.count) begin
            n_time_reset++;
            if (TS_FORMAT == 1) begin
                reanchor_pending = 1;
                `uvm_info(this.get_full_name(), $sformatf(
                          "TIME_RESET assertion #%0d observed -> epoch re-anchor armed", n_time_reset), UVM_LOW)
            end else begin
                `uvm_info(this.get_full_name(), $sformatf(
                          "TIME_RESET assertion #%0d observed -> ignored (TS_FORMAT=0 has no epoch)",
                          n_time_reset), UVM_HIGH)
            end
        end
    endtask

    task run_model();
        uvm_logic_vector_array::sequence_item #(ITEM_WIDTH)     tr_data_in;
        uvm_logic_vector::sequence_item #(EXTENDED_META_WIDTH)  tr_meta_in;
        uvm_packet_delayer::delayer_data_item #(ITEM_WIDTH)     tr_data_out;
        uvm_packet_delayer::delayer_meta_item #(META_WIDTH)     tr_meta_out;

        logic [TS_WIDTH-1:0] ts;
        logic [TS_WIDTH-1:0] ts_prev;
        int unsigned         n;
        time                 t_arr;
        time                 t_mon;
        time                 t_mon0;
        time                 t_ts;
        time                 t_hol;
        time                 t_arr_br;
        time                 hol_clks;
        time                 t_sof_rx;
        time                 t_eof_rx;
        time                 t_eof_prev;
        time                 words_span;
        int unsigned         words_prev;
        bit                  share_prev;
        bit                  first;

        first      = 1;
        words_prev = 1;
        t_eof_prev = 0ns;
        t_mon      = 0ns;
        t_mon0     = 0ns;

        forever begin
            data_in.get(tr_data_in);
            meta_in.get(tr_meta_in);
            m_n_pkts++;

            consume_time_reset();

            // Timestamp, frame length and RX monitor stamps
            // (t_sof_rx = META stamp/SOF, t_eof_rx = data stamp/EOF)
            ts       = tr_meta_in.data[TS_WIDTH-1:0];
            t_arr    = tr_meta_in.time_last();
            t_sof_rx = t_arr;
            t_eof_rx = tr_data_in.time_last();
            n        = tr_data_in.data.size();

            // Sharing with the previous frame (same MFB word); REGIONS > 1 only
            share_prev = (!first) && (t_sof_rx <= t_eof_prev);

            if (TS_FORMAT == 0) begin
                // ---------------- Interval timestamps -----------------------
                if (first) begin
                    // First packet: the reset anchor bounds the release
                    t_mon = tmax2(reset_sync.stop_time + ts * TICK + PIPE_LAT * TICK,
                                  t_arr    + (ARRIV_LAT + PIPE_LAT) * TICK);
                    first = 0;
                end else begin
                    // Interval from the previously released packet, or late arrival
                    t_mon = tmax2(t_mon + ts * TICK,
                                  t_arr + (ARRIV_LAT + PIPE_LAT) * TICK);
                end
            end else begin
                // ---------------- Absolute timestamps -----------------------
                // Sanity: TS_FORMAT=1 timestamps must increase. The packet that
                // applies a TIME_RESET re-anchor starts a fresh epoch, so its
                // (re-based) timestamp legitimately restarts below the previous.
                if ((!first) && (!reanchor_pending) && (ts <= ts_prev)) begin
                    `uvm_error(this.get_full_name(), $sformatf(
                               "TS_FORMAT=1: timestamp is not strictly increasing (%0d <= %0d)", ts, ts_prev))
                end

                // Head-of-line: never below one clock
                hol_clks = ((words_prev - share_prev) > 1 ? (words_prev - share_prev) : 1) + GAP_TIME;

                if (first || reanchor_pending) begin
                    if (first) begin
                        // First packet: no head-of-line; this release anchors the rest
                        t_mon = tmax2(reset_sync.stop_time + ts * TICK + PIPE_LAT * TICK,
                                      t_arr    + (ARRIV_LAT + PIPE_LAT) * TICK);
                    end else begin
                        // TIME_RESET re-anchor: the DUT re-armed its epoch, so the
                        // next SOF (this packet) becomes the new epoch. The stale
                        // reset-anchored schedule no longer applies; the release is
                        // bounded below by the arrival latency and the head-of-line.
                        t_mon = tmax2(t_arr + (ARRIV_LAT + PIPE_LAT) * TICK,
                                      t_mon + hol_clks * TICK);
                    end
                    t_mon0           = t_mon;
                    first            = 0;
                    reanchor_pending = 0;
                    `uvm_info(this.get_full_name(), $sformatf(
                              "Epoch re-anchor at packet n=%0d: new t_mon0=%0t", n, t_mon0), UVM_LOW)
                end else begin
                    // Absolute, anchored at the first released SOF
                    t_ts = t_mon0 + ts * TICK;

                    t_hol    = t_mon + hol_clks * TICK;

                    // Late arrival
                    t_arr_br = t_arr + (ARRIV_LAT + PIPE_LAT) * TICK;

                    t_mon = tmax3(t_ts, t_hol, t_arr_br);
                end
            end

            // Word span: boolean test (a raw stamp difference would over-count)
            words_span = (t_eof_rx > t_sof_rx) ? TICK : 0;

            // Build output items (meta = SOF release, data = EOF release)
            tr_data_out = uvm_packet_delayer::delayer_data_item #(ITEM_WIDTH)::type_id::create("tr_data_out");
            tr_data_out.data             = tr_data_in.data;
            tr_data_out.expected_release = t_mon + words_span;

            tr_meta_out = uvm_packet_delayer::delayer_meta_item #(META_WIDTH)::type_id::create("tr_meta_out");
            tr_meta_out.data             = tr_meta_in.data[EXTENDED_META_WIDTH-1:TS_WIDTH];
            tr_meta_out.expected_release = t_mon;

            // Emit at the EOF time
            if ((t_mon + words_span) > $time()) begin
                #((t_mon + words_span) - $time());
            end

            tr_data_out.start["model"] = $time();
            tr_meta_out.start["model"] = $time();
            data_out.write(tr_data_out);
            meta_out.write(tr_meta_out);

            `uvm_info(this.get_full_name(), $sformatf(
                      {"Packet ts=%0d n=%0d t_sof_rx=%0t t_eof_rx=%0t span=%0t share='b%0b",
                       " -> t_mon(SOF)=%0t EOF=%0t"},
                      ts, n, t_sof_rx, t_eof_rx, words_span, share_prev,
                      t_mon, tr_data_out.expected_release), UVM_HIGH)

            // Remember the word count / EOF stamp for the next frame
            words_prev = (t_eof_rx > t_sof_rx) ? 2 : 1;
            t_eof_prev = t_eof_rx;
            ts_prev    = ts;
        end
    endtask

    task run_phase(uvm_phase phase);
        run_model();
    endtask
endclass
