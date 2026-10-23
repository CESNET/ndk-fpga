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

    START_META_WIDTH        : integer := 1;
    END_META_WIDTH          : integer := 1;
    DEVICE                  : string  := "ULTRASCALE"
);
port(
    CLK                     : in  std_logic;
    RST                     : in  std_logic;

    START_EVENT             : in  std_logic;
    START_EVENT_META        : in  std_logic_vector(START_META_WIDTH - 1 downto 0) := (others => '0');

    END_EVENT               : in  std_logic;
    END_EVENT_META          : in  std_logic_vector(END_META_WIDTH - 1 downto 0) := (others => '0');

    LATENCY_VLD             : out std_logic;
    LATENCY                 : out std_logic_vector(DATA_WIDTH - 1 downto 0);
    LATENCY_START_META      : out std_logic_vector(START_META_WIDTH - 1 downto 0);
    LATENCY_END_META        : out std_logic_vector(END_META_WIDTH - 1 downto 0);

    -- Signals that no more paralel events can be curently measured
    FIFO_FULL               : out std_logic;
    -- Number of paralel latencies in FIFO
    FIFO_ITEMS              : out std_logic_vector(max(log2(MAX_PARALEL_EVENTS), 1) downto 0)
);
end entity;

architecture FULL of LATENCY_METER is

    type OUTPUT_T is record
        start_event : std_logic;
        end_event   : std_logic;
        tick_cnt    : std_logic_vector(DATA_WIDTH - 1 downto 0);
        start_meta  : std_logic_vector(START_META_WIDTH - 1 downto 0);
        end_meta    : std_logic_vector(END_META_WIDTH - 1 downto 0);
    end record;

    type OUTPUT_ARRAY_T is array (integer range <>) of OUTPUT_T;

    constant DATA_MAX           : std_logic_vector(DATA_WIDTH - 1 downto 0) := (others => '1');
    constant OUTPUT_STAGES      : positive := 3;

    signal fifo_out             : std_logic_vector(DATA_WIDTH + START_META_WIDTH - 1 downto 0);
    signal start_meta_i         : std_logic_vector(START_META_WIDTH - 1 downto 0);

    signal tick_cnt             : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal start_ticks          : std_logic_vector(DATA_WIDTH - 1 downto 0);
    signal tick_limit           : std_logic;
    signal tick_ovf             : std_logic;
    signal fifo_empty           : std_logic;
    signal zero_delay           : std_logic;

    signal output_in            : OUTPUT_ARRAY_T(OUTPUT_STAGES - 1 downto 0);
    signal output_out           : OUTPUT_ARRAY_T(OUTPUT_STAGES - 1 downto 0);
    signal fin_out              : OUTPUT_T;

begin

    -------------------------
    -- Component instances --
    -------------------------

    fifo_i : entity work.FIFOX
    generic map (
        DATA_WIDTH  => DATA_WIDTH + START_META_WIDTH,
        ITEMS       => MAX_PARALEL_EVENTS,
        DEVICE      => DEVICE
    )
    port map (
        CLK         => CLK,
        RESET       => RST,

        DI          => (tick_cnt, START_EVENT_META),
        WR          => START_EVENT,
        FULL        => FIFO_FULL,
        STATUS      => FIFO_ITEMS,

        DO          => fifo_out,
        RD          => fin_out.end_event,
        EMPTY       => fifo_empty
    );

    (start_ticks, start_meta_i) <= fifo_out;

    -------------------------
    -- Combinational logic --
    -------------------------

    tick_limit  <= '1' when (tick_cnt = DATA_MAX) else
                   '0';

    tick_ovf    <= '1' when (fin_out.tick_cnt < start_ticks) else
                   '0';

    zero_delay  <= fin_out.start_event and fin_out.end_event and fifo_empty;

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

    output_g : for i in OUTPUT_STAGES - 1 downto 0 generate
        output_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RST = '1') then
                    output_out(i).start_event   <= '0';
                    output_out(i).end_event     <= '0';
                else
                    output_out(i)               <= output_in(i);
                end if;
            end if;
        end process;

        output_copy_g : if i > 0 generate
            output_in(i)    <= output_out(i - 1);
        end generate;
    end generate;

    output_in(0).start_event    <= START_EVENT;
    output_in(0).start_meta     <= start_meta_i;

    output_in(0).end_event      <= END_EVENT;
    output_in(0).end_meta       <= END_EVENT_META;

    output_in(0).tick_cnt       <= tick_cnt;

    fin_out                     <= output_out(OUTPUT_STAGES - 1);

    latency_vld_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            -- An end without a stored start has no latency to report; the FIFO ignores that read.
            LATENCY_VLD         <= (fin_out.end_event and (not fifo_empty)) or zero_delay;
            LATENCY             <= (others => '0')                                          when (zero_delay = '1') else
                       std_logic_vector(unsigned(fin_out.tick_cnt) - unsigned(start_ticks)) when (tick_ovf = '0')   else
                       std_logic_vector(unsigned(fin_out.tick_cnt) + unsigned(DATA_MAX) - unsigned(start_ticks) + 1);

            LATENCY_START_META  <= fin_out.start_meta;
            LATENCY_END_META    <= fin_out.end_meta;
        end if;
    end process;

end architecture;

