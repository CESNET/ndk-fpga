-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Component AXIS_MERGER is used to merge N input AXI Stream interfaces into one
-- output AXI Stream interface. The merging is done in random order.
--
entity AXIS_MERGER is
    generic (
        -- width of AXI-Stream data signal in bits
        TDATA_WIDTH   : natural := 512;
        -- width of AXI-Stream user signal in bits
        TUSER_WIDTH   : natural := 64;
        -- number of RX AXI-Stream interfaces
        RX_STREAMS    : natural := 32;
        -- target device: AGILEX, STRATIX10, ULTRASCALE,...
        DEVICE        : string  := "AGILEX";
        -- maximum number of packets before switching channel
        MAX_PACKETS   : natural := 4;
        -- adds register to the output
        OUT_REG       : boolean := true
    );
    port (
        -- =========================================================================
        -- Clock and reset signals
        -- =========================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =========================================================================
        -- RX AXI-Stream interfaces (CLK)
        -- =========================================================================
        RX_AXIS_TDATA  : in  slv_array_t(RX_STREAMS-1 downto 0)(TDATA_WIDTH-1 downto 0);
        RX_AXIS_TUSER  : in  slv_array_t(RX_STREAMS-1 downto 0)(TUSER_WIDTH-1 downto 0);
        RX_AXIS_TKEEP  : in  slv_array_t(RX_STREAMS-1 downto 0)(TDATA_WIDTH/8-1 downto 0);
        RX_AXIS_TLAST  : in  std_logic_vector(RX_STREAMS-1 downto 0);
        RX_AXIS_TVALID : in  std_logic_vector(RX_STREAMS-1 downto 0);
        RX_AXIS_TREADY : out std_logic_vector(RX_STREAMS-1 downto 0);

        -- =========================================================================
        -- TX AXI-Stream interface (CLK)
        -- =========================================================================
        TX_AXIS_TDATA  : out std_logic_vector(TDATA_WIDTH-1 downto 0);
        TX_AXIS_TUSER  : out std_logic_vector(TUSER_WIDTH-1 downto 0);
        TX_AXIS_TKEEP  : out std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        TX_AXIS_TLAST  : out std_logic;
        TX_AXIS_TVALID : out std_logic;
        TX_AXIS_TREADY : in  std_logic
    );
end entity;

architecture FULL of AXIS_MERGER is
    -- async
    signal sel_log     : unsigned(log2(RX_STREAMS)-1 downto 0);
    signal pkt_cnt_log : unsigned(log2(MAX_PACKETS)-1 downto 0);
    signal switch_chan : std_logic;
    signal ready       : std_logic_vector(RX_STREAMS-1 downto 0);
    signal last        : std_logic;

    -- sync
    signal selector    : unsigned(log2(RX_STREAMS)-1 downto 0);
    signal packet_cnt  : unsigned(log2(MAX_PACKETS)-1 downto 0);

begin

    -- =========================================================================
    -- Input
    -- =========================================================================
    RX_AXIS_TREADY <= ready when TX_AXIS_TREADY = '1' else (others => '0');

    -- =========================================================================
    -- Logic
    -- =========================================================================

    -- Picks a new stream that has RX_AXIS_TVALID set to 1. If none does,
    -- keeps the same stream.
    selector_logic_p : process (all)
        variable new_sel : unsigned(log2(RX_STREAMS)-1 downto 0) := (others => '0');
    begin
        sel_log <= selector;
        new_sel := selector + 1;

        for i in 0 to RX_STREAMS-1 loop
            if (RX_AXIS_TVALID(to_integer(new_sel)) = '1') then
                sel_log <= new_sel;
                exit;
            else
                new_sel := new_sel + 1;
            end if;
        end loop;
    end process;

    -- Counts packets. End of a packet is determined by the 'last' signal.
    pkt_cntr_p : process (all)
    begin
        pkt_cnt_log <= packet_cnt;

        if (last = '1') then
            pkt_cnt_log <= packet_cnt + 1;
        end if;

        if (switch_chan = '1') then
            pkt_cnt_log <= (others => '0');
        end if;
    end process;

    -- Activates logic switching the selected stream if the maximum number of
    -- packets per stream has been reached or if after the end of a packet
    -- the chosen stream no longer has valid data (RX_AXIS_TVALID = '0').
    switch_chan_logic_p : process (all)
    begin
        switch_chan <= '0';

        if (last = '1') then
            if ((packet_cnt = MAX_PACKETS - 1) or (RX_AXIS_TVALID(to_integer(selector)) = '0')) then
                switch_chan <= '1';
            end if;
        end if;
    end process;

    -- Activates RX_AXIS_TREADY signal only for the selected stream.
    ready_logic_p : process (all)
    begin
        ready                       <= (others => '0');
        ready(to_integer(selector)) <= '1';
    end process;

    -- Sets the signal 'last', which is used to preserve the information about
    -- the end of a packet being reached.
    last_logic_p : process (all)
    begin
        if RX_AXIS_TVALID(to_integer(selector)) then
            if (RX_AXIS_TLAST(to_integer(selector)) = '1') then
                last <= '1';
            else
                if (last = '1') then
                    last <= '0';
                end if;
            end if;
        end if;

        if (RESET = '1') then
            last <= '1';
        end if;
    end process;

    -- =========================================================================
    -- Registers
    -- =========================================================================
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXIS_TREADY = '1' and switch_chan = '1') then
                selector <= sel_log;
            end if;

            if (RESET = '1') then
                selector <= (others => '0');
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXIS_TREADY = '1') then
                packet_cnt <= pkt_cnt_log;
            end if;

            if (RESET = '1') then
                packet_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- =========================================================================
    -- Output
    -- =========================================================================
    output_register_g: if OUT_REG generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                if (TX_AXIS_TREADY = '1') then
                    TX_AXIS_TDATA  <= RX_AXIS_TDATA(to_integer(selector));
                    TX_AXIS_TUSER  <= RX_AXIS_TUSER(to_integer(selector));
                    TX_AXIS_TKEEP  <= RX_AXIS_TKEEP(to_integer(selector));
                    TX_AXIS_TLAST  <= RX_AXIS_TLAST(to_integer(selector));
                    TX_AXIS_TVALID <= RX_AXIS_TVALID(to_integer(selector));
                end if;

                if (RESET = '1') then
                    TX_AXIS_TVALID <= '0';
                end if;
            end if;
        end process;
    else generate
        TX_AXIS_TDATA  <= RX_AXIS_TDATA(to_integer(selector));
        TX_AXIS_TUSER  <= RX_AXIS_TUSER(to_integer(selector));
        TX_AXIS_TKEEP  <= RX_AXIS_TKEEP(to_integer(selector));
        TX_AXIS_TLAST  <= RX_AXIS_TLAST(to_integer(selector));
        TX_AXIS_TVALID <= RX_AXIS_TVALID(to_integer(selector));
    end generate;

end architecture;
