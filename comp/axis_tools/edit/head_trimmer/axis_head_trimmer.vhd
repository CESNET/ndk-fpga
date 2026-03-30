-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Removes a configurable number of bytes from the beginning of AXI-Stream packets.
-- Uses a 2-stage input shift register with barrel shifter for data alignment.
-- Trim instruction (length and enable) is sampled at the first word of each packet
-- and applied to the entire packet. Guaranteed throughput: 1 word per clock cycle.
--
entity AXIS_HEAD_TRIMMER is
    generic (
        -- AXI-Stream data bus width in bits; must be a multiple of 8.
        AXI_TDATA_WIDTH  : natural := 512;
        -- Maximum packet length (MTU) in bytes. Used to size the byte counter.
        PKT_MTU          : natural := 9216;  -- Jumbo frame support
        -- Target device.
        DEVICE           : string := "AGILEX"
    );
    port (
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- RX Interface
        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- Trim instruction interface (sampled only at the first word of each packet)
        -- Number of bytes to remove from the beginning of the packet.
        -- Valid range: 0 to packet_length-1 (at least one byte must remain).
        RX_AXI_TRIM_LENGTH : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        -- Enable trim operation for this packet. When low, packet passes through unchanged.
        RX_AXI_TRIM_ENABLE : in  std_logic;

        -- TX Interface
        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;

architecture FULL of AXIS_HEAD_TRIMMER is

    constant WORD_BYTES      : natural := AXI_TDATA_WIDTH/8;
    constant OFF_BYTES_W     : natural := log2(WORD_BYTES);
    constant TRIM_LEN_W      : natural := log2(PKT_MTU+1);
    constant SHREG_STAGES    : natural := 2;
    constant BS_BLOCKS       : natural := 2*WORD_BYTES;
    constant POPCOUNT_W      : natural := log2(WORD_BYTES+1);

    signal valid_word          : std_logic;
    signal rx_axi_eop          : std_logic;
    signal rx_axi_sop          : std_logic;
    signal rx_axi_nonfirst_reg : std_logic;

    signal rx_axi_trim_length_reg : std_logic_vector(TRIM_LEN_W-1 downto 0);
    signal rx_axi_trim_enable_reg : std_logic;

    signal popcount          : unsigned(POPCOUNT_W-1 downto 0);
    signal byte_cnt_reg      : unsigned(TRIM_LEN_W-1 downto 0);
    signal byte_cnt_next     : unsigned(TRIM_LEN_W-1 downto 0);

    signal trim_pos_ok       : std_logic;
    signal trim_pos_next_ok  : std_logic;
    signal trim_active       : std_logic;
    signal trim_last         : std_logic;

    signal shreg_popcount    : u_array_t(SHREG_STAGES downto 0)(POPCOUNT_W-1 downto 0);
    signal shreg_byte_cnt    : u_array_t(SHREG_STAGES downto 0)(TRIM_LEN_W-1 downto 0);
    signal shreg_tdata       : slv_array_t(SHREG_STAGES downto 0)(AXI_TDATA_WIDTH-1 downto 0);
    signal shreg_tkeep       : slv_array_t(SHREG_STAGES downto 0)(WORD_BYTES-1 downto 0);
    signal shreg_tfirst      : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_tlast       : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_tvalid      : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_trim_len    : u_array_t(SHREG_STAGES downto 0)(TRIM_LEN_W-1 downto 0);
    signal shreg_trim_en     : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_trim_active : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_trim_last   : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_ready       : std_logic_vector(SHREG_STAGES downto 0);
    signal shreg_ok          : std_logic;
    signal shreg_tvalid_fix  : std_logic;

    signal buf_tdata       : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal buf_tkeep       : std_logic_vector(WORD_BYTES-1 downto 0);
    signal buf_tfirst      : std_logic;
    signal buf_tlast       : std_logic;
    signal buf_tvalid      : std_logic;
    signal buf_tready      : std_logic;
    signal buf_trim_len    : unsigned(TRIM_LEN_W-1 downto 0);
    signal buf_trim_en     : std_logic;
    signal buf_trim_active : std_logic;
    signal buf_trim_last   : std_logic;
    signal buf_popcount    : unsigned(POPCOUNT_W-1 downto 0);
    signal buf_byte_cnt    : unsigned(TRIM_LEN_W-1 downto 0);
    signal buf_2word_bytes : unsigned(log2(2*WORD_BYTES+1)-1 downto 0);
    signal buf_next_bytes  : unsigned(log2(2*WORD_BYTES+1)-1 downto 0);
    signal buf_new_keep    : std_logic_vector(WORD_BYTES-1 downto 0);

    signal buf_trim_shift     : unsigned(OFF_BYTES_W-1 downto 0);
    signal buf_trim_shift_reg : unsigned(OFF_BYTES_W-1 downto 0);
    signal buf_trim_post      : std_logic;

    signal bs_shift          : unsigned(OFF_BYTES_W-1 downto 0);
    signal bs_din            : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);
    signal bs_dout           : std_logic_vector(2*AXI_TDATA_WIDTH-1 downto 0);

    signal tx_tdata_next     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_tkeep_next     : std_logic_vector(WORD_BYTES-1 downto 0);
    signal tx_tlast_next     : std_logic;
    signal tx_tlast_next_reg : std_logic;
    signal tx_tvalid_next    : std_logic;
    signal tx_tdata_reg      : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_tkeep_reg      : std_logic_vector(WORD_BYTES-1 downto 0);
    signal tx_tlast_reg      : std_logic;
    signal tx_tvalid_reg     : std_logic;

begin

    RX_AXI_TREADY <= shreg_ready(0);

    valid_word <= RX_AXI_TVALID and RX_AXI_TREADY;
    rx_axi_eop <= RX_AXI_TLAST and valid_word;

    -- Detect first beat of each packet for packet counter
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or rx_axi_eop = '1') then
                rx_axi_nonfirst_reg <= '0';
            elsif (valid_word = '1') then
                rx_axi_nonfirst_reg <= '1';
            end if;
        end if;
    end process;

    rx_axi_sop <= valid_word and not rx_axi_nonfirst_reg;

    popcount <= to_unsigned(count_ones(RX_AXI_TKEEP), POPCOUNT_W);

    -- Byte counter accumulates total bytes received in current packet
    byte_cnt_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (valid_word = '1') then
                if (RX_AXI_TLAST = '1') then
                    byte_cnt_reg <= (others => '0');
                else
                    byte_cnt_reg <= byte_cnt_next;
                end if;
            end if;
            if (RESET = '1') then
                byte_cnt_reg <= (others => '0');
            end if;
        end if;
    end process;

    byte_cnt_next <= byte_cnt_reg + popcount;

    -- Capture trim instruction at packet start, hold for entire packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_axi_sop = '1') then
                rx_axi_trim_length_reg <= RX_AXI_TRIM_LENGTH;
                rx_axi_trim_enable_reg <= RX_AXI_TRIM_ENABLE;
            end if;
            if (RESET = '1') then
                rx_axi_trim_enable_reg <= '0';
            end if;
        end if;
    end process;

    -- Detect if current/next position is within the trim region
    trim_pos_ok      <= '1' when (byte_cnt_reg <= shreg_trim_len(0)) else '0';
    trim_pos_next_ok <= '1' when (byte_cnt_next <= shreg_trim_len(0)) else '0';

    -- trim_active: entire word is trimmed (skipped)
    -- trim_last: word contains the trim boundary (partial trim)
    trim_active <= shreg_trim_en(0) and trim_pos_next_ok;
    trim_last   <= shreg_trim_en(0) and trim_pos_ok and not trim_pos_next_ok;

    shreg_tdata(0)    <= RX_AXI_TDATA;
    shreg_tkeep(0)    <= RX_AXI_TKEEP;
    shreg_tfirst(0)   <= rx_axi_sop;
    shreg_tlast(0)    <= RX_AXI_TLAST;
    shreg_tvalid(0)   <= RX_AXI_TVALID;
    shreg_byte_cnt(0) <= byte_cnt_reg;
    shreg_popcount(0) <= popcount;

    shreg_trim_len(0)    <= unsigned(RX_AXI_TRIM_LENGTH) when (rx_axi_sop = '1') else unsigned(rx_axi_trim_length_reg);
    shreg_trim_en(0)     <= RX_AXI_TRIM_ENABLE           when (rx_axi_sop = '1') else rx_axi_trim_enable_reg;
    shreg_trim_active(0) <= trim_active;
    shreg_trim_last(0)   <= trim_last;

    shreg_g: for i in 0 to SHREG_STAGES-1 generate
        shreg_p : process (CLK)
        begin
            if rising_edge(CLK) then
                if (shreg_ready(i) = '1') then
                    shreg_tdata(i+1)       <= shreg_tdata(i);
                    shreg_tkeep(i+1)       <= shreg_tkeep(i);
                    shreg_tfirst(i+1)      <= shreg_tfirst(i);
                    shreg_tlast(i+1)       <= shreg_tlast(i);
                    shreg_tvalid(i+1)      <= shreg_tvalid(i);
                    shreg_trim_len(i+1)    <= shreg_trim_len(i);
                    shreg_trim_en(i+1)     <= shreg_trim_en(i);
                    shreg_trim_active(i+1) <= shreg_trim_active(i);
                    shreg_trim_last(i+1)   <= shreg_trim_last(i);
                    shreg_byte_cnt(i+1)    <= shreg_byte_cnt(i);
                    shreg_popcount(i+1)    <= shreg_popcount(i);
                end if;
                if (RESET = '1') then
                    shreg_tvalid(i+1)  <= '0';
                    shreg_trim_en(i+1) <= '0';
                end if;
            end if;
        end process;

        shreg_ready(i) <= shreg_ready(i+1) or not shreg_tvalid(i+1);
    end generate;

    -- Backpressure: stall input when output not ready or insufficient data in pipeline
    shreg_ready(SHREG_STAGES) <= buf_tready and shreg_ok;
    shreg_tvalid_fix          <= shreg_ok;

    -- shreg_ok indicates valid data can be presented at output
    shreg_ok <= (shreg_tvalid(SHREG_STAGES) and shreg_tvalid(SHREG_STAGES-1)) or
                (shreg_tvalid(SHREG_STAGES) and shreg_tlast(SHREG_STAGES-1));

    buf_tdata       <= shreg_tdata(SHREG_STAGES);
    buf_tkeep       <= shreg_tkeep(SHREG_STAGES);
    buf_tfirst      <= shreg_tfirst(SHREG_STAGES);
    buf_tlast       <= shreg_tlast(SHREG_STAGES);
    buf_tvalid      <= shreg_tvalid_fix;
    buf_trim_len    <= shreg_trim_len(SHREG_STAGES);
    buf_trim_en     <= shreg_trim_en(SHREG_STAGES);
    buf_trim_active <= shreg_trim_active(SHREG_STAGES);
    buf_trim_last   <= shreg_trim_last(SHREG_STAGES);
    buf_byte_cnt    <= shreg_byte_cnt(SHREG_STAGES);
    buf_popcount    <= shreg_popcount(SHREG_STAGES);

    buf_tready <= TX_AXI_TREADY;

    -- Calculate shift amount: how many bytes to shift for alignment after trim
    buf_trim_shift <= resize(shreg_trim_len(SHREG_STAGES) - shreg_byte_cnt(SHREG_STAGES), OFF_BYTES_W);

    -- Calculate total valid bytes in 2-word window (current + previous)
    process (all)
    begin
        buf_2word_bytes <= resize(shreg_popcount(SHREG_STAGES), log2(2*WORD_BYTES+1)) + shreg_popcount(SHREG_STAGES-1);
        if (shreg_tlast(SHREG_STAGES) = '1') then
            buf_2word_bytes <= resize(shreg_popcount(SHREG_STAGES), log2(2*WORD_BYTES+1));
        end if;
    end process;

    -- Remaining bytes after applying barrel shifter offset
    buf_next_bytes <= buf_2word_bytes - bs_shift;

    -- Generate TKEEP for partial last word based on remaining byte count
    process (all)
    begin
        buf_new_keep <= (others => '0');
        for i in 0 to WORD_BYTES-1 loop
            if (buf_next_bytes > i) then
                buf_new_keep(i) <= '1';
            end if;
        end loop;
    end process;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (buf_trim_last = '1') then
                buf_trim_shift_reg <= buf_trim_shift;
            end if;
        end if;
    end process;

    -- Track post-trim state for multi-word packets
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (buf_tvalid = '1' and buf_tready = '1') then
                if (buf_trim_last = '1') then
                    buf_trim_post <= '1';
                end if;
                if (buf_tlast = '1') then
                    buf_trim_post <= '0';
                end if;
            end if;
            if (RESET = '1') then
                buf_trim_post <= '0';
            end if;
        end if;
    end process;

    -- Select barrel shifter offset: current trim boundary or registered value for post-trim alignment
    bs_shift <= buf_trim_shift     when (buf_trim_last = '1') else
                buf_trim_shift_reg when (buf_trim_post = '1') else
                (others => '0');

    bs_din(2*AXI_TDATA_WIDTH-1 downto AXI_TDATA_WIDTH) <= shreg_tdata(SHREG_STAGES-1);
    bs_din(AXI_TDATA_WIDTH-1 downto 0)                 <= shreg_tdata(SHREG_STAGES);

    barrel_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => BS_BLOCKS,
        BLOCK_SIZE => 8,
        SHIFT_LEFT => false
    )
    port map (
        DATA_IN  => bs_din,
        DATA_OUT => bs_dout,
        SEL      => std_logic_vector(resize(bs_shift, log2(BS_BLOCKS)))
    );

    tx_tdata_next <= bs_dout(AXI_TDATA_WIDTH-1 downto 0);

    -- TKEEP: all ones for full word, otherwise generate partial keep pattern
    tx_tkeep_next <= (others => '1') when (buf_next_bytes >= WORD_BYTES) else buf_new_keep;

    -- TLAST asserted when remaining bytes fit in current word
    tx_tlast_next <= '1' when (buf_next_bytes <= WORD_BYTES) else '0';

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (buf_tvalid = '1' and buf_tready = '1') then
                if (tx_tlast_next = '1') then
                    tx_tlast_next_reg <= '1';
                end if;
                if (buf_tlast = '1') then
                    tx_tlast_next_reg <= '0';
                end if;
            end if;
            if (RESET = '1') then
                tx_tlast_next_reg <= '0';
            end if;
        end if;
    end process;

    -- Suppress TVALID during trim and for one cycle after TLAST to handle word skipping
    tx_tvalid_next <= buf_tvalid and not (buf_trim_active or tx_tlast_next_reg);

    output_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                tx_tdata_reg  <= tx_tdata_next;
                tx_tkeep_reg  <= tx_tkeep_next;
                tx_tlast_reg  <= tx_tlast_next;
                tx_tvalid_reg <= tx_tvalid_next;
            end if;
            if (RESET = '1') then
                tx_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    TX_AXI_TDATA  <= tx_tdata_reg;
    TX_AXI_TKEEP  <= tx_tkeep_reg;
    TX_AXI_TLAST  <= tx_tlast_reg;
    TX_AXI_TVALID <= tx_tvalid_reg;

end architecture;
