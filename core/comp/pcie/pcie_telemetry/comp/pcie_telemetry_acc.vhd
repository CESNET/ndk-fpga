-- pcie_telemetry_acc.vhd: Wide counter memory fed by telemetry probes
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The PCIE_TELEMETRY_ACC merges the delta streams of all telemetry probes into
-- one memory of wide free-running counters. The deltas arrive one by one, so a
-- single adder and a single memory are enough for all channels.
--
-- The memory holds two copies of the counters. The deltas update the live copy.
-- The SNAPSHOT command writes the snapshot copy. Software reads the snapshot
-- copy, so all values it reads belong to the same moment, even though reading
-- them takes many bus transactions.
--
-- Deltas keep arriving while a SNAPSHOT or CLEAR command runs. They wait in the
-- probe FIFOs and are applied when the command is done.
--
entity PCIE_TELEMETRY_ACC is
    generic (
        -- Number of delta streams (probes).
        STREAMS     : natural := 2;
        -- First counter index of each stream.
        STREAM_BASE : i_array_t := (0,16);
        -- Number of counters. It must be a power of two.
        ENTRIES     : natural := 64;
        -- Width of the channel index of a delta.
        IDX_WIDTH   : natural := 5;
        -- Width of the value of a delta.
        DELTA_WIDTH : natural := 14;
        -- Width of the counters in the memory.
        CNT_WIDTH   : natural := 48
    );
    port (
        CLK       : in  std_logic;
        RESET     : in  std_logic;

        -- =====================================================================
        --  DELTA STREAMS
        -- =====================================================================
        RX_INDEX  : in  slv_array_t(STREAMS-1 downto 0)(IDX_WIDTH-1 downto 0);
        RX_DELTA  : in  slv_array_t(STREAMS-1 downto 0)(DELTA_WIDTH-1 downto 0);
        RX_VLD    : in  std_logic_vector(STREAMS-1 downto 0);
        RX_RD     : out std_logic_vector(STREAMS-1 downto 0);

        -- =====================================================================
        --  COMMANDS
        -- =====================================================================
        -- Copies the live counters into the snapshot copy.
        SNAPSHOT  : in  std_logic;
        -- Zeroes both copies of the counters.
        CLEAR     : in  std_logic;
        -- A command is in progress. Deltas are not applied while it runs.
        BUSY      : out std_logic;

        -- =====================================================================
        --  SOFTWARE READ PORT
        -- =====================================================================
        -- The highest bit selects the copy, 0 = live, 1 = snapshot.
        RD_ADDR   : in  std_logic_vector(log2(ENTRIES)+1-1 downto 0);
        RD_EN     : in  std_logic;
        RD_DATA   : out std_logic_vector(CNT_WIDTH-1 downto 0)
    );
end entity;

architecture FULL of PCIE_TELEMETRY_ACC is

    constant ADDR_WIDTH : natural := log2(ENTRIES)+1;

    type fsm_t is (ST_IDLE, ST_ACC_RD, ST_ACC_ADD, ST_ACC_WR, ST_SNAP_RD, ST_SNAP_WR, ST_CLEAR);

    signal fsm_pst      : fsm_t;
    signal snap_req     : std_logic;
    signal clear_req    : std_logic;

    signal sel          : natural range 0 to STREAMS-1;
    signal sel_next     : natural range 0 to STREAMS-1;
    signal sel_vld      : std_logic;

    signal acc_addr_reg : unsigned(ADDR_WIDTH-1 downto 0);
    signal acc_data_reg : unsigned(CNT_WIDTH-1 downto 0);
    signal acc_sum_reg  : unsigned(CNT_WIDTH-1 downto 0);
    signal sweep_cnt    : unsigned(ADDR_WIDTH-1 downto 0);

    signal pa_addr      : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal pa_we        : std_logic;
    signal pa_re        : std_logic;
    signal pa_din       : std_logic_vector(CNT_WIDTH-1 downto 0);
    signal pa_dout      : std_logic_vector(CNT_WIDTH-1 downto 0);

begin

    assert (2**log2(ENTRIES) = ENTRIES)
        report "PCIE_TELEMETRY_ACC: Set ENTRIES to a power of two."
        severity failure;

    -- =========================================================================
    --  STREAM SELECTION
    -- =========================================================================

    -- Round robin starting behind the stream served last, so no stream has to
    -- wait while a busier one is served again.
    process (all)
    begin
        sel_next <= sel;
        sel_vld  <= '0';
        for i in STREAMS-1 downto 0 loop
            if (RX_VLD((sel+1+i) mod STREAMS) = '1') then
                sel_next <= (sel+1+i) mod STREAMS;
                sel_vld  <= '1';
            end if;
        end loop;
    end process;

    rx_rd_g : for i in 0 to STREAMS-1 generate
        RX_RD(i) <= '1' when (fsm_pst = ST_ACC_RD and sel = i) else '0';
    end generate;

    -- =========================================================================
    --  COMMAND AND ACCUMULATION FSM
    -- =========================================================================

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- A command may arrive while the memory is busy. It is served as
            -- soon as the current delta is written.
            if (SNAPSHOT = '1') then
                snap_req <= '1';
            end if;
            if (CLEAR = '1') then
                clear_req <= '1';
            end if;

            case (fsm_pst) is
                when ST_IDLE =>
                    if (clear_req = '1') then
                        clear_req <= '0';
                        sweep_cnt <= (others => '0');
                        fsm_pst   <= ST_CLEAR;
                    elsif (snap_req = '1') then
                        snap_req  <= '0';
                        sweep_cnt <= (others => '0');
                        fsm_pst   <= ST_SNAP_RD;
                    elsif (sel_vld = '1') then
                        sel     <= sel_next;
                        fsm_pst <= ST_ACC_RD;
                    end if;

                when ST_ACC_RD =>
                    -- The live copy sits in the lower half of the memory.
                    acc_addr_reg <= resize(to_unsigned(STREAM_BASE(sel),ADDR_WIDTH)
                                           + unsigned(RX_INDEX(sel)),ADDR_WIDTH);
                    acc_data_reg <= resize(unsigned(RX_DELTA(sel)),CNT_WIDTH);
                    fsm_pst      <= ST_ACC_ADD;

                when ST_ACC_ADD =>
                    acc_sum_reg <= unsigned(pa_dout) + acc_data_reg;
                    fsm_pst     <= ST_ACC_WR;

                when ST_ACC_WR =>
                    -- Chaining directly into the next read saves one cycle per
                    -- delta, the write of this delta is already done.
                    if (clear_req = '0' and snap_req = '0' and sel_vld = '1') then
                        sel     <= sel_next;
                        fsm_pst <= ST_ACC_RD;
                    else
                        fsm_pst <= ST_IDLE;
                    end if;

                when ST_SNAP_RD =>
                    fsm_pst <= ST_SNAP_WR;

                when ST_SNAP_WR =>
                    if (sweep_cnt = ENTRIES-1) then
                        fsm_pst <= ST_IDLE;
                    else
                        sweep_cnt <= sweep_cnt + 1;
                        fsm_pst   <= ST_SNAP_RD;
                    end if;

                when ST_CLEAR =>
                    if (sweep_cnt = 2*ENTRIES-1) then
                        fsm_pst <= ST_IDLE;
                    else
                        sweep_cnt <= sweep_cnt + 1;
                    end if;
            end case;

            if (RESET = '1') then
                fsm_pst   <= ST_IDLE;
                sel       <= 0;
                sweep_cnt <= (others => '0');
                snap_req  <= '0';
                clear_req <= '0';
            end if;
        end if;
    end process;

    -- Software polls BUSY to learn when a command has finished, so a waiting
    -- command must be reported as busy too.
    BUSY <= '0' when (fsm_pst /= ST_CLEAR and fsm_pst /= ST_SNAP_RD and
                      fsm_pst /= ST_SNAP_WR and snap_req = '0' and clear_req = '0') else
 '1';

    -- =========================================================================
    --  COUNTER MEMORY
    -- =========================================================================

    process (all)
    begin
        pa_addr <= std_logic_vector(acc_addr_reg);
        pa_re   <= '0';
        pa_we   <= '0';
        pa_din  <= std_logic_vector(acc_sum_reg);

        case (fsm_pst) is
            when ST_ACC_RD =>
                -- The address is not registered yet, take it directly.
                pa_addr <= std_logic_vector(resize(to_unsigned(STREAM_BASE(sel),ADDR_WIDTH)
                                                   + unsigned(RX_INDEX(sel)),ADDR_WIDTH));
                pa_re   <= '1';

            when ST_ACC_WR =>
                pa_we <= '1';

            when ST_SNAP_RD =>
                pa_addr <= '0' & std_logic_vector(sweep_cnt(ADDR_WIDTH-2 downto 0));
                pa_re   <= '1';

            when ST_SNAP_WR =>
                pa_addr <= '1' & std_logic_vector(sweep_cnt(ADDR_WIDTH-2 downto 0));
                pa_din  <= pa_dout;
                pa_we   <= '1';

            when ST_CLEAR =>
                pa_addr <= std_logic_vector(sweep_cnt);
                pa_din  <= (others => '0');
                pa_we   <= '1';

            when others =>
                null;
        end case;
    end process;

    bram_i : entity work.DP_BRAM_BEHAV
    generic map (
        DATA_WIDTH => CNT_WIDTH,
        ITEMS      => 2**ADDR_WIDTH,
        OUTPUT_REG => False,
        RDW_MODE_A => "WRITE_FIRST",
        RDW_MODE_B => "WRITE_FIRST"
    )
    port map (
        CLK      => CLK,
        RST      => RESET,

        PIPE_ENA => '1',
        REA      => pa_re,
        WEA      => pa_we,
        ADDRA    => pa_addr,
        DIA      => pa_din,
        DOA      => pa_dout,
        DOA_DV   => open,

        PIPE_ENB => '1',
        REB      => RD_EN,
        WEB      => '0',
        ADDRB    => RD_ADDR,
        DIB      => (others => '0'),
        DOB      => RD_DATA,
        DOB_DV   => open
    );

end architecture;
