-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- AXIS_TAIL_TRIMMER removes bytes from the end (tail) of AXI-Stream packets to
-- achieve a configured packet length. The trim_length input specifies the desired
-- packet length in bytes. If the packet exceeds this length, excess bytes from
-- the end are removed. The trim instruction (length and enable) is sampled at the
-- first word of each packet and remains valid for the entire packet duration.
-- The module guarantees throughput of 1 word per clock cycle.
--
entity AXIS_TAIL_TRIMMER is
    generic (
        -- AXI-Stream data bus width in bits (must be multiple of 8)
        AXI_TDATA_WIDTH  : natural := 512;
        -- Maximum packet length (MTU) in bytes - determines byte counter width
        PKT_MTU          : natural := 9216;
        -- Target device technology
        DEVICE           : string := "AGILEX"
    );
    port (
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- AXI-Stream RX interface
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- Trim instruction sampled at packet start
        -- trim_length: target packet length in bytes (bytes beyond this are removed)
        RX_AXI_TRIM_LENGTH : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        -- trim_enable: when '1', packets longer than trim_length are truncated
        RX_AXI_TRIM_ENABLE : in  std_logic;

        -- AXI-Stream TX interface
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;

architecture FULL of AXIS_TAIL_TRIMMER is

    constant WORD_BYTES      : natural := AXI_TDATA_WIDTH/8;
    constant TRIM_LEN_W      : natural := log2(PKT_MTU+1);
    constant POPCOUNT_W      : natural := log2(WORD_BYTES+1);

    -- Input stage signals
    signal rx_valid_word     : std_logic;
    signal rx_sop            : std_logic;
    signal rx_in_packet      : std_logic;
    signal rx_popcount       : unsigned(POPCOUNT_W-1 downto 0);

    -- Byte counter - tracks cumulative byte count within packet
    signal byte_cnt          : unsigned(TRIM_LEN_W-1 downto 0);
    signal byte_cnt_next     : unsigned(TRIM_LEN_W-1 downto 0);

    -- Trim configuration captured at packet start
    signal cfg_trim_len      : unsigned(TRIM_LEN_W-1 downto 0);
    signal cfg_trim_en       : std_logic;

    -- Output stage registers
    signal tx_tdata_reg      : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_tkeep_reg      : std_logic_vector(WORD_BYTES-1 downto 0);
    signal tx_tlast_reg      : std_logic;
    signal tx_tvalid_reg     : std_logic;

    -- Trimmer control signals
    signal trim_en           : std_logic;
    signal trim_len          : unsigned(TRIM_LEN_W-1 downto 0);
    signal trim_start        : std_logic;
    signal trim_whole_word   : std_logic;
    signal trim_inactive     : std_logic;
    signal trim_bytes_diff   : unsigned(POPCOUNT_W-1 downto 0);
    signal trim_tdata        : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal trim_tkeep        : std_logic_vector(WORD_BYTES-1 downto 0);
    signal trim_tlast        : std_logic;
    signal trim_tvalid       : std_logic;

begin

    ---------------------------------------------------------------------------
    -- Input Stage
    -- Handles backpressure propagation and packet boundary detection
    ---------------------------------------------------------------------------

    -- Pass TX ready directly to RX (no internal buffering)
    RX_AXI_TREADY <= TX_AXI_TREADY;
    rx_valid_word <= RX_AXI_TVALID and TX_AXI_TREADY;

    -- Track whether we are currently inside a packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                rx_in_packet <= '0';
            elsif (rx_valid_word = '1') then
                rx_in_packet <= not RX_AXI_TLAST;
            end if;
        end if;
    end process;

    -- SOP detected when valid word arrives and we were not in a packet
    rx_sop <= rx_valid_word and not rx_in_packet;

    ---------------------------------------------------------------------------
    -- Byte Counter
    -- Counts bytes within each packet, resets at packet boundary
    ---------------------------------------------------------------------------

    rx_popcount <= to_unsigned(count_ones(RX_AXI_TKEEP), POPCOUNT_W);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_valid_word = '1') then
                if (RX_AXI_TLAST = '1') then
                    byte_cnt <= (others => '0');  -- Reset at end of packet
                else
                    byte_cnt <= byte_cnt_next;
                end if;
            end if;
            if (RESET = '1') then
                byte_cnt <= (others => '0');
            end if;
        end if;
    end process;

    byte_cnt_next <= byte_cnt + resize(rx_popcount, TRIM_LEN_W);

    ---------------------------------------------------------------------------
    -- Trim Configuration Capture
    -- Samples trim instruction at start of each packet
    ---------------------------------------------------------------------------

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_sop = '1') then
                cfg_trim_len <= unsigned(RX_AXI_TRIM_LENGTH);
                cfg_trim_en  <= RX_AXI_TRIM_ENABLE;
            end if;
            if (RESET = '1') then
                cfg_trim_en <= '0';
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- Trimmer Stage
    -- Applies tail trimming by masking TKEEP and adjusting TLAST
    ---------------------------------------------------------------------------

    -- Hold trim configuration for entire packet duration
    trim_en  <= RX_AXI_TRIM_ENABLE           when (rx_sop = '1') else cfg_trim_en;
    trim_len <= unsigned(RX_AXI_TRIM_LENGTH) when (rx_sop = '1') else cfg_trim_len;

    -- Assert trim_start when next byte count reaches or exceeds trim length
    trim_start <= '1' when (byte_cnt_next >= trim_len) else '0';

    -- Track when entire word should be trimmed (from trim_start to packet end)
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_valid_word = '1') then
                if (trim_start = '1') then
                    trim_whole_word <= trim_en;
                end if;
                if (RX_AXI_TLAST = '1') then
                    trim_whole_word <= '0';
                end if;
            end if;
            if (RESET = '1') then
                trim_whole_word <= '0';
            end if;
        end if;
    end process;

    -- Trimming is inactive when enabled but trim_start/trim_whole_word not asserted
    trim_inactive <= trim_en and not (trim_start or trim_whole_word);

    -- Data passes through unchanged; trimming is done via TKEEP masking
    trim_tdata <= RX_AXI_TDATA;

    -- Calculate bytes remaining before reaching trim point
    trim_bytes_diff <= resize((trim_len - byte_cnt), POPCOUNT_W);

    -- Generate TKEEP mask to trim excess bytes from packet tail
    process (all)
    begin
        trim_tkeep <= (others => '0');
        for i in 0 to WORD_BYTES-1 loop
            if (trim_bytes_diff > i) then
                trim_tkeep(i) <= '1';
            end if;
        end loop;

        -- Keep all bytes when trimming is not active
        if (trim_inactive = '1') then
            trim_tkeep <= (others => '1');
        end if;

        -- Pass original TKEEP when trimming is disabled
        if (trim_en = '0') then
            trim_tkeep <= RX_AXI_TKEEP;
        end if;
    end process;

    -- Assert TLAST at trim point to terminate packet early
    trim_tlast  <= trim_start when (trim_en = '1') else RX_AXI_TLAST;
    -- Suppress valid when word is being trimmed
    trim_tvalid <= RX_AXI_TVALID and not trim_whole_word;

    ---------------------------------------------------------------------------
    -- Output Register Stage
    ---------------------------------------------------------------------------

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                tx_tdata_reg  <= trim_tdata;
                tx_tkeep_reg  <= trim_tkeep;
                tx_tlast_reg  <= trim_tlast;
                tx_tvalid_reg <= trim_tvalid;
            end if;
            if (RESET = '1') then
                tx_tdata_reg  <= (others => '0');
                tx_tkeep_reg  <= (others => '0');
                tx_tlast_reg  <= '0';
                tx_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    TX_AXI_TDATA  <= tx_tdata_reg;
    TX_AXI_TKEEP  <= tx_tkeep_reg;
    TX_AXI_TLAST  <= tx_tlast_reg;
    TX_AXI_TVALID <= tx_tvalid_reg;

end architecture;
