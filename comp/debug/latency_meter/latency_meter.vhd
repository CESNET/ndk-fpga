-- dut.vhd: Wrapped DRAM_SEARCH_TREE + MI_ADAPTER
-- Read/Write change test
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- .. vhdl:autogenerics:: LATENCY_METER
entity LATENCY_METER is
generic (
    -- Tick counter width (defines max. latency)
    DATA_WIDTH              : integer;
    -- Defines max. number of parallel events that can be measured
    MAX_PARALEL_EVENTS      : integer := 1;
    DEVICE                  : string  := "ULTRASCALE"
);
port(
    CLK                     : in  std_logic;
    RST                     : in  std_logic;

    START_EVENT             : in  std_logic;
    END_EVENT               : in  std_logic;

    LATENCY_VLD             : out std_logic;
    LATENCY                 : out std_logic_vector(DATA_WIDTH - 1 downto 0);

    -- Signals that no more paralel events can be curently measured
    FIFO_FULL               : out std_logic;
    -- Number of paralel latencies in FIFO
    FIFO_ITEMS              : out std_logic_vector(max(log2(MAX_PARALEL_EVENTS), 1) downto 0)
);
end entity;

architecture FULL of LATENCY_METER is

    constant DATA_MAX           : std_logic_vector(DATA_WIDTH - 1 downto 0) := (others => '1');

    signal tick_cnt             : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal start_ticks          : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal tick_limit           : std_logic;
    signal tick_ovf             : std_logic;
    signal fifo_empty           : std_logic;
    signal zero_delay           : std_logic;

    signal end_event_delay_0    : std_logic;
    signal end_event_delay_1    : std_logic;
    signal end_event_delay_2    : std_logic;

    signal start_event_delay_0  : std_logic;
    signal start_event_delay_1  : std_logic;
    signal start_event_delay_2  : std_logic;

    signal tick_cnt_delay_0     : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal tick_cnt_delay_1     : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal tick_cnt_delay_2     : std_logic_vector(DATA_WIDTH - 1 downto 0);

begin

    -------------------------
    -- Component instances --
    -------------------------

    fifo_i : entity work.FIFOX
    generic map (
        DATA_WIDTH  => DATA_WIDTH,
        ITEMS       => MAX_PARALEL_EVENTS,
        DEVICE      => DEVICE
    )
    port map (
        CLK         => CLK,
        RESET       => RST,

        DI          => tick_cnt,
        WR          => START_EVENT,
        FULL        => FIFO_FULL,
        STATUS      => FIFO_ITEMS,

        DO          => start_ticks,
        RD          => end_event_delay_2,
        EMPTY       => fifo_empty
    );

    -------------------------
    -- Combinational logic --
    -------------------------

    tick_limit  <= '1' when (tick_cnt = DATA_MAX) else
                   '0';

    tick_ovf    <= '1' when (tick_cnt_delay_2 < start_ticks) else
                   '0';

    zero_delay  <= start_event_delay_2 and end_event_delay_2 and fifo_empty;

    ---------------
    -- Registers --
    ---------------

    tick_cnt_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RST = '1' or tick_limit = '1') then
                tick_cnt    <= (others => '0');
            else
                tick_cnt    <= std_logic_vector(unsigned(tick_cnt) + 1);
            end if;
        end if;
    end process;

    latency_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            LATENCY <= (others => '0')                                                      when (zero_delay = '1') else
                       std_logic_vector(unsigned(tick_cnt_delay_2) - unsigned(start_ticks)) when (tick_ovf = '0')   else
                       std_logic_vector(unsigned(tick_cnt_delay_2) + unsigned(DATA_MAX) - unsigned(start_ticks) + 1);
        end if;
    end process;

    latency_vld_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            LATENCY_VLD <= end_event_delay_2;
        end if;
    end process;

    delay_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            end_event_delay_0   <= END_EVENT;
            end_event_delay_1   <= end_event_delay_0;
            end_event_delay_2   <= end_event_delay_1;

            start_event_delay_0 <= START_EVENT;
            start_event_delay_1 <= start_event_delay_0;
            start_event_delay_2 <= start_event_delay_1;

            tick_cnt_delay_0    <= tick_cnt;
            tick_cnt_delay_1    <= tick_cnt_delay_0;
            tick_cnt_delay_2    <= tick_cnt_delay_1;
        end if;
    end process;

end architecture;

