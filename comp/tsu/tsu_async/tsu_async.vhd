-- tsu_async.vhd:
-- Copyright (C) 2025 CESNET z.s.p.o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- This component is used to synchronize timestamps between two clock domains.
-- An asynchronous FIFO is used internally. If its output is invalid, the last
-- valid timestamp is used, but only for the set timeout period.
--
entity TSU_ASYNC is
    generic (
        TIMEOUT_W  : natural := 3;
        FIFO_DEPTH : natural := 32;
        DEVICE     : string  := "ULTRASCALE"
    );
    port (
        IN_CLK         : in  std_logic;
        IN_RESET       : in  std_logic;
        IN_TS          : in  std_logic_vector(64-1 downto 0) := (others => '0');
        IN_TS_NS       : in  std_logic_vector(64-1 downto 0) := (others => '0');
        IN_TS_DV       : in  std_logic;

        OUT_CLK        : in  std_logic;
        OUT_RESET      : in  std_logic;
        OUT_TS         : out std_logic_vector(64-1 downto 0);
        OUT_TS_NS      : out std_logic_vector(64-1 downto 0);
        OUT_TS_DV      : out std_logic
    );
end entity;

architecture FULL of TSU_ASYNC is

    constant TS_W      : natural := 64;

    signal fifo_di     : std_logic_vector(2*TS_W-1 downto 0);
    signal fifo_do     : std_logic_vector(2*TS_W-1 downto 0);
    signal fifo_dv_n   : std_logic;

    signal timeout_cnt : unsigned(TIMEOUT_W-1 downto 0);
    signal was_valid   : std_logic;

begin

    fifo_di(TS_W-1 downto 0)      <= IN_TS_NS;
    fifo_di(2*TS_W-1 downto TS_W) <= IN_TS;

    asfifox_i : entity work.ASFIFOX
    generic map (
        DATA_WIDTH => 2*TS_W,
        ITEMS      => FIFO_DEPTH,
        RAM_TYPE   => "LUT",
        FWFT_MODE  => true,
        OUTPUT_REG => true,
        DEVICE     => DEVICE
    )
    port map (
        WR_CLK    => IN_CLK,
        WR_RST    => IN_RESET,
        WR_DATA   => fifo_di,
        WR_EN     => IN_TS_DV,
        WR_FULL   => open,
        WR_AFULL  => open,
        WR_STATUS => open,

        RD_CLK    => OUT_CLK,
        RD_RST    => OUT_RESET,
        RD_DATA   => fifo_do,
        RD_EN     => '1',
        RD_EMPTY  => fifo_dv_n,
        RD_AEMPTY => open,
        RD_STATUS => open
    );

    process (OUT_CLK)
    begin
        if (rising_edge(OUT_CLK)) then
            if ((fifo_dv_n = '1') and (timeout_cnt(TIMEOUT_W-1) = '0')) then
                timeout_cnt <= timeout_cnt + 1;
            end if;
            if ((OUT_RESET = '1') or (fifo_dv_n = '0')) then
                timeout_cnt <= (others => '0');
            end if;
        end if;
    end process;

    process (OUT_CLK)
    begin
        if (rising_edge(OUT_CLK)) then
            if (fifo_dv_n = '0') then
                was_valid <= '1';
            end if;
            if (OUT_RESET = '1') then
                was_valid <= '0';
            end if;
        end if;
    end process;

    -- Synced TS is valid if the value is current or if the value is a few
    -- clock cycles old. This provides filtering for occasional flushing of
    -- the asynchronous FIFO.
    process (OUT_CLK)
    begin
        if (rising_edge(OUT_CLK)) then
            if (fifo_dv_n = '0') then
                OUT_TS_NS <= fifo_do(TS_W-1 downto 0);
                OUT_TS    <= fifo_do(2*TS_W-1 downto TS_W);
            end if;

            OUT_TS_DV <= (not fifo_dv_n) or (was_valid and not timeout_cnt(TIMEOUT_W-1));

            if (OUT_RESET = '1') then
                OUT_TS_DV <= '0';
            end if;
        end if;
    end process;

end architecture;
