-- axis_eth_parser_sniffer.vhd: AXI-Stream Ethernet Parser Sniffer
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The AXIS_ETH_PARSER_SNIFFER component extracts a contiguous block of bytes
-- from an AXI-Stream data flow at a specified offset. The component uses a
-- barrel shifter to align the data and a state machine to track extraction
-- progress across multiple AXI words. Metadata (protocol type and offset) is
-- passed through the component to maintain context for downstream parser stages.
-- The AXI-Stream data passes through with one cycle latency.
--
entity AXIS_ETH_PARSER_SNIFFER is
    generic (
        -- Width of the AXI-Stream data bus in bits (must be power of two, e.g., 256, 512)
        AXI_TDATA_WIDTH    : natural := 512;
        -- Number of bytes to extract from the header
        EXTRACT_BYTES      : natural := 32;
        -- Maximum packet size in bytes (determines offset field width)
        PKT_MTU            : natural := 2**14;
        -- Width of metadata field (protocol + offset information)
        META_WIDTH         : natural := 32;
        -- Target device family for implementation (e.g., "AGILEX", "ULTRASCALE")
        DEVICE             : string  := "AGILEX"
    );
    port (
        -- System clock
        CLK                   : in  std_logic;
        -- Active-high synchronous reset
        RESET                 : in  std_logic;

        -- RX AXI-Stream Interface
        RX_AXI_TDATA          : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        RX_AXI_TKEEP          : in  std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        RX_AXI_TLAST          : in  std_logic;
        RX_AXI_TVALID         : in  std_logic;
        RX_AXI_TREADY         : out std_logic;

        -- TX AXI-Stream Interface
        TX_AXI_TDATA          : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        TX_AXI_TKEEP          : out std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
        TX_AXI_TLAST          : out std_logic;
        TX_AXI_TVALID         : out std_logic;
        TX_AXI_TREADY         : in  std_logic;

        -- Start metadata (protocol and offset for extraction)
        START_META            : in  std_logic_vector(META_WIDTH-1 downto 0);
        -- Start byte offset within the frame
        START_OFFSET          : in  std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
        -- Start extraction enable
        START_ENABLE          : in  std_logic;
        -- Start extraction valid
        START_VALID           : in  std_logic;

        -- Extracted metadata (passed through from START_META)
        EXTRACTED_META        : out std_logic_vector(META_WIDTH-1 downto 0);
        -- Extracted header data (EXTRACT_BYTES bytes)
        EXTRACTED_DATA        : out std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
        -- Extracted data valid
        EXTRACTED_VALID       : out std_logic
    );
end entity;

architecture FULL of AXIS_ETH_PARSER_SNIFFER is

    -- Number of bytes per AXI word
    constant WORD_BYTES      : natural := AXI_TDATA_WIDTH/8;
    -- Width of the offset field in bits (derived from PKT_MTU)
    constant OFFSET_WIDTH    : natural := log2(PKT_MTU+1);
    -- Bits required for byte offset within an AXI word
    constant OFF_BYTES_W     : natural := log2(WORD_BYTES);
    -- Bits required for word offset within the frame
    constant OFF_WORDS_W     : natural := OFFSET_WIDTH - OFF_BYTES_W;
    -- Bits required for byte counter
    constant BYTES_CNT_W     : natural := log2(EXTRACT_BYTES + 1);
    -- Bits required for bytes-to-extract counter
    constant WORD_BYTES_W    : natural := log2(WORD_BYTES+1);

    -- AXI word tracking
    signal valid_word           : std_logic;
    signal end_word             : std_logic;
    signal word_cnt             : unsigned(OFF_WORDS_W-1 downto 0);

    -- AXI register stage signals
    signal tx_axi_tdata_reg     : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal tx_axi_tkeep_reg     : std_logic_vector((AXI_TDATA_WIDTH/8)-1 downto 0);
    signal tx_axi_tlast_reg     : std_logic;
    signal tx_axi_tvalid_reg    : std_logic;

    -- Start offset and metadata latching
    signal start_offset_reg     : unsigned(OFFSET_WIDTH-1 downto 0);
    signal start_valid_reg      : std_logic;
    signal start_enable_reg     : std_logic;
    signal soff                 : unsigned(OFFSET_WIDTH-1 downto 0);
    signal soff_word            : unsigned(OFF_WORDS_W-1 downto 0);
    signal soff_bytes           : unsigned(OFF_BYTES_W-1 downto 0);
    signal soff_vld             : std_logic;
    signal word_ok              : std_logic;
    signal word_ok_set          : std_logic;
    signal enable_flag          : std_logic;

    -- Extraction state machine
    signal extracting           : std_logic;
    signal bytes_extracted      : unsigned(BYTES_CNT_W-1 downto 0);
    signal bytes_remaining      : unsigned(BYTES_CNT_W-1 downto 0);
    signal bytes_remaining_now  : unsigned(BYTES_CNT_W-1 downto 0);
    signal extraction_complete  : std_logic;

    -- Metadata registers
    signal start_meta_reg       : std_logic_vector(META_WIDTH-1 downto 0);
    signal extracted_meta_reg   : std_logic_vector(META_WIDTH-1 downto 0);

    -- Barrel shifter signals
    signal shift_amount         : unsigned(OFF_BYTES_W-1 downto 0);
    signal shifted_data         : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);

    -- Extracted data registers
    signal extracted_data_reg   : std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
    signal extracted_data_next  : std_logic_vector(EXTRACT_BYTES*8-1 downto 0);
    signal extracted_done_reg   : std_logic;
    signal extracted_vld        : std_logic;
    signal extracted_vld_reg    : std_logic;

    -- Bytes to extract in current cycle
    signal bytes_to_extract     : unsigned(WORD_BYTES_W-1 downto 0);

begin

    -- AXI word valid and last word detection
    valid_word <= RX_AXI_TVALID and TX_AXI_TREADY;
    end_word   <= RX_AXI_TLAST and valid_word;

    -- Word counter tracks position within packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                word_cnt <= (others => '0');
            elsif (valid_word = '1') then
                word_cnt <= word_cnt + 1;
            end if;
        end if;
    end process;

    -- AXI register stage provides one cycle latency for data path
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                tx_axi_tdata_reg  <= (others => '0');
                tx_axi_tkeep_reg  <= (others => '0');
                tx_axi_tlast_reg  <= '0';
                tx_axi_tvalid_reg <= '0';
            elsif (TX_AXI_TREADY = '1') then
                tx_axi_tdata_reg  <= RX_AXI_TDATA;
                tx_axi_tkeep_reg  <= RX_AXI_TKEEP;
                tx_axi_tlast_reg  <= RX_AXI_TLAST;
                tx_axi_tvalid_reg <= RX_AXI_TVALID;
            end if;
        end if;
    end process;

    TX_AXI_TDATA  <= tx_axi_tdata_reg;
    TX_AXI_TKEEP  <= tx_axi_tkeep_reg;
    TX_AXI_TLAST  <= tx_axi_tlast_reg;
    TX_AXI_TVALID <= tx_axi_tvalid_reg;
    RX_AXI_TREADY <= TX_AXI_TREADY;

    -- Latch start offset and metadata when extraction begins
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (START_VALID = '1') then
                start_offset_reg <= unsigned(START_OFFSET);
                start_valid_reg  <= '1';
                start_meta_reg   <= START_META;
                start_enable_reg <= START_ENABLE;
            end if;
            if ((RESET = '1') or (end_word = '1')) then
                start_valid_reg <= '0';
            end if;
        end if;
    end process;

    -- Current start offset (combinational or registered)
    soff       <= unsigned(START_OFFSET) when (START_VALID = '1') else start_offset_reg;
    soff_vld   <= start_valid_reg or START_VALID;
    soff_word  <= soff(OFFSET_WIDTH-1 downto OFF_BYTES_W);
    soff_bytes <= soff(OFF_BYTES_W-1 downto 0);

    enable_flag <= START_ENABLE when (START_VALID = '1') else start_enable_reg;

    -- Word matches target offset when word counter equals offset word field
    word_ok <= '1' when (soff_vld = '1' and soff_word = word_cnt) else '0';

    -- Calculate number of bytes to extract in current cycle
    process (all)
    begin
        if ((extracting = '1') and (valid_word = '1')) then
            if (bytes_extracted = 0) then
                -- First extraction word: extract from soff_bytes to end of AXI word
                if ((WORD_BYTES - to_integer(soff_bytes)) < to_integer(bytes_remaining)) then
                    bytes_to_extract <= to_unsigned(WORD_BYTES, WORD_BYTES_W) - soff_bytes;
                else
                    bytes_to_extract <= resize(bytes_remaining, WORD_BYTES_W);
                end if;
            else
                -- Subsequent words: extract full AXI word or remaining bytes
                if (WORD_BYTES < bytes_remaining) then
                    bytes_to_extract <= to_unsigned(WORD_BYTES, WORD_BYTES_W);
                else
                    bytes_to_extract <= resize(bytes_remaining, WORD_BYTES_W);
                end if;
            end if;
        else
            bytes_to_extract <= to_unsigned(0, WORD_BYTES_W);
        end if;
    end process;

    -- Shift amount for barrel shifter (only for first extraction word)
    shift_amount <= soff_bytes when (bytes_extracted = 0 and extracting = '1') else (others => '0');

    -- Barrel shifter aligns data to extraction start position
    barrel_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => WORD_BYTES,
        BLOCK_SIZE => 8,
        SHIFT_LEFT => false
    )
    port map (
        DATA_IN  => RX_AXI_TDATA,
        DATA_OUT => shifted_data,
        SEL      => std_logic_vector(shift_amount)
    );

    -- Calculate next extracted data value by inserting shifted bytes
    process (all)
        variable start_idx : natural;
    begin
        extracted_data_next <= extracted_data_reg;

        start_idx := to_integer(bytes_extracted);
        if ((bytes_to_extract > 0) and (start_idx < EXTRACT_BYTES)) then
            for i in 0 to WORD_BYTES-1 loop
                if ((i < to_integer(bytes_to_extract)) and ((start_idx + i) < EXTRACT_BYTES)) then
                    extracted_data_next((start_idx+i+1)*8-1 downto (start_idx+i)*8) <= shifted_data((i+1)*8-1 downto i*8);
                end if;
            end loop;
        end if;
    end process;

    -- Track when extraction window begins
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                word_ok_set <= '0';
            elsif (word_ok = '1' and valid_word = '1') then
                word_ok_set <= '1';
            end if;
        end if;
    end process;

    -- Extraction active from target word until end of packet
    extracting <= word_ok or word_ok_set;

    -- Track extracted byte count and remaining bytes
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                bytes_extracted <= (others => '0');
                bytes_remaining <= to_unsigned(EXTRACT_BYTES, bytes_remaining'length);
            elsif (extracting = '1' and valid_word = '1') then
                bytes_extracted <= bytes_extracted + resize(bytes_to_extract, BYTES_CNT_W);
                bytes_remaining <= bytes_remaining - resize(bytes_to_extract, BYTES_CNT_W);
            end if;
        end if;
    end process;

    -- Extraction complete when all requested bytes have been captured
    bytes_remaining_now <= bytes_remaining - resize(bytes_to_extract, BYTES_CNT_W);
    extraction_complete <= '1' when (bytes_remaining_now = 0) else '0';

    -- Store extracted data bytes
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (extracting = '1' and valid_word = '1') then
                extracted_data_reg <= extracted_data_next;
            end if;
        end if;
    end process;

    -- Track when extraction is done
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1' or end_word = '1') then
                extracted_done_reg <= '0';
            elsif (extraction_complete = '1') then
                extracted_done_reg <= '1';
            end if;
        end if;
    end process;

    -- Generate valid pulse when extraction completes or packet ends
    extracted_vld <= (extraction_complete and not extracted_done_reg) or
                     (end_word and not extraction_complete and not extracted_done_reg);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                extracted_vld_reg <= '0';
            elsif (enable_flag = '1') then
                extracted_vld_reg <= extracted_vld;
            else
                extracted_vld_reg <= valid_word and word_ok and not word_ok_set;
            end if;
        end if;
    end process;

    -- Store metadata for output
    process (CLK)
    begin
        if rising_edge(CLK) then
            extracted_meta_reg <= START_META when (START_VALID = '1') else start_meta_reg;
        end if;
    end process;

    -- Drive extracted data outputs
    EXTRACTED_META  <= extracted_meta_reg;
    EXTRACTED_DATA  <= extracted_data_reg;
    EXTRACTED_VALID <= extracted_vld_reg;

end architecture;
