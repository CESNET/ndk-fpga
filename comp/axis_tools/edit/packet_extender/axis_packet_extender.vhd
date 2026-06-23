-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- AXIS_PACKET_EXTENDER prepends a configurable number of random bytes to each
-- AXI-Stream packet. The extension length (RX_AXI_EXT_LEN) is sampled at the
-- first word (SOP) of every packet.
-- The original packet data is shifted by the extension length in bytes,
-- so the original payload follows the first N output bytes with random values.
--
-- Currently, the maximum extension cannot be more than a word.
--
entity AXIS_PACKET_EXTENDER is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH  : natural := 512;
        -- AXI-Stream metadata bus width in bits, valid with SOP.
        AXI_TUSER_WIDTH  : natural := 11;
        -- Bit-width of extension length signal.
        -- Max extend value is 2**EXT_LEN_WIDTH - 1 bytes.
        EXT_LEN_WIDTH    : natural := 5
    );
    port (
        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- ========================================================
        -- AXI-Stream RX interface.
        -- ========================================================

        RX_AXI_TDATA     : in  std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        -- User metadata, valid with SOP.
        RX_AXI_TUSER     : in  std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
        RX_AXI_TKEEP     : in  std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        RX_AXI_TLAST     : in  std_logic;
        RX_AXI_TVALID    : in  std_logic;
        RX_AXI_TREADY    : out std_logic;

        -- Extension length in bytes, valid with SOP (first word of each packet).
        RX_AXI_EXT_LEN   : in  std_logic_vector(EXT_LEN_WIDTH-1 downto 0);

        -- ========================================================
        -- AXI-Stream TX interface.
        -- ========================================================

        TX_AXI_TDATA     : out std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
        -- User metadata, valid with SOP.
        TX_AXI_TUSER     : out std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
        TX_AXI_TKEEP     : out std_logic_vector(AXI_TDATA_WIDTH/8-1 downto 0);
        TX_AXI_TLAST     : out std_logic;
        TX_AXI_TVALID    : out std_logic;
        TX_AXI_TREADY    : in  std_logic
    );
end entity;

-- ===========================================================================
-- ARCHITECTURE
-- ===========================================================================
architecture FULL of AXIS_PACKET_EXTENDER is

    constant DATA_BYTES   : natural := AXI_TDATA_WIDTH/8;
    constant DATA_BYTES_W : natural := log2(DATA_BYTES);
    constant EXT_CNT_W    : natural := EXT_LEN_WIDTH-work.math_pack.min(EXT_LEN_WIDTH, DATA_BYTES_W);

    -- SOP detection / handshake
    signal rx_valid_word        : std_logic;
    signal rx_sop               : std_logic;
    signal rx_in_packet         : std_logic;
    signal rx_ready             : std_logic;

    -- Input register
    signal rx_tdata_reg         : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx_tuser_reg         : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal rx_tkeep_reg         : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx_tlast_reg         : std_logic;
    signal rx_tvalid_reg        : std_logic;
    
    signal extend_len           : unsigned(max(EXT_LEN_WIDTH, DATA_BYTES_W)-1 downto 0);
    signal extend_len_reg       : unsigned(max(EXT_LEN_WIDTH, DATA_BYTES_W)-1 downto 0);

    -- Barrel shifter signals
    signal bs_din               : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal bs_dout              : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal bs_shift             : std_logic_vector(DATA_BYTES_W-1 downto 0);

    -- Output combinational logic
    signal tx_tdata             : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal tx_tuser             : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal tx_tkeep             : std_logic_vector(DATA_BYTES-1 downto 0);
    signal tx_tlast             : std_logic;
    signal tx_tvalid            : std_logic;

    signal tkeep_ones_extended  : unsigned(DATA_BYTES_W+1-1 downto 0);
    signal tkeep_ones_spilled   : unsigned(DATA_BYTES_W-1 downto 0);
    signal will_spill           : std_logic;
    signal sending_spill        : std_logic;
    signal spilled_tdata        : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal shifted_tdata        : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);

    signal byte_ptr             : integer range 0 to DATA_BYTES-1;
    signal keep_ptr             : integer range 0 to 2*DATA_BYTES-1;

begin

    assert EXT_LEN_WIDTH < DATA_BYTES_W
        report "AXIS_PACKET_EXTENDER: Extend length set too high! Cannot extend by more bytes than are in a single dataword."
        severity Failure;

    -- ===========================================================================
    -- Input stage / SOP detection
    -- ===========================================================================

    RX_AXI_TREADY <= rx_ready;
    rx_valid_word <= RX_AXI_TVALID and rx_ready;

    -- Track whether we are currently inside a packet
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_valid_word = '1') then
                rx_in_packet <= not RX_AXI_TLAST;
            end if;
            if (RESET = '1') then
                rx_in_packet <= '0';
            end if;
        end if;
    end process;

    -- SOP detected when a valid (handshaked) word arrives outside a packet.
    rx_sop <= rx_valid_word and not rx_in_packet;

    -- ===========================================================================
    -- Input register
    -- ===========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_ready = '1') then
                rx_tdata_reg  <= slv_array_deser(RX_AXI_TDATA, DATA_BYTES);
                rx_tuser_reg  <= RX_AXI_TUSER;
                rx_tkeep_reg  <= RX_AXI_TKEEP;
                rx_tlast_reg  <= RX_AXI_TLAST;
                rx_tvalid_reg <= RX_AXI_TVALID;
            end if;
            if (RESET = '1') then
                rx_tvalid_reg <= '0';
            end if;
        end if;
    end process;

    -- Extend length sampled at Start-Of-Packet.
    extend_len <= resize(unsigned(RX_AXI_EXT_LEN), max(EXT_LEN_WIDTH, DATA_BYTES_W)) when (rx_sop = '1') else extend_len_reg;
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_ready = '1') then
                extend_len_reg      <= extend_len;
                tkeep_ones_extended <= to_unsigned(count_ones(RX_AXI_TKEEP), DATA_BYTES_W+1) + resize(extend_len, DATA_BYTES_W+1) - 1;
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- Shifting RX data
    -- ===========================================================================

    bs_din   <= slv_array_ser(rx_tdata_reg);
    bs_shift <= std_logic_vector(resize(extend_len_reg, DATA_BYTES_W));

    -- Shift data from the RX reg
    rx1_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => DATA_BYTES,
        BLOCK_SIZE => 8,
        SHIFT_LEFT => true
    )
    port map (
        DATA_IN  => bs_din,
        DATA_OUT => bs_dout,
        SEL      => bs_shift
    );

    -- ===========================================================================
    -- TX data finalization
    -- ===========================================================================

    shifted_tdata <= slv_array_deser(bs_dout, DATA_BYTES);

    -- Boundary where the extension data ends and the packet data begins.
    byte_ptr <= to_integer(resize(extend_len_reg, DATA_BYTES_W));
    -- Boundary where the (shifted) packet ends within the word.
    keep_ptr <= to_integer(tkeep_ones_spilled) when (sending_spill = '1') else to_integer(tkeep_ones_extended);

    -- The last word will spill into one extra word after sifting.
    will_spill <= rx_tlast_reg and rx_tvalid_reg and -- There is a valid tlast and
                  tkeep_ones_extended(DATA_BYTES_W) and -- the number of valid bytes + extension bytes go over the dataword's capacity.
                  not sending_spill; -- Reset after the spill part is sent.

    tx_logic_g : for db in 0 to DATA_BYTES-1 generate
        tx_tdata(db) <= spilled_tdata(db) when (db <  byte_ptr) else shifted_tdata(db);
        tx_tkeep(db) <= '1'               when (db <= keep_ptr) else '0';
    end generate;
    tx_tuser  <= rx_tuser_reg;
    tx_tlast  <= (rx_tlast_reg and not will_spill) or sending_spill;
    tx_tvalid <= rx_tvalid_reg or sending_spill;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                sending_spill      <= will_spill and rx_tlast_reg;
                tkeep_ones_spilled <= tkeep_ones_extended(DATA_BYTES_W-1 downto 0);
            end if;
            if (RESET = '1') then
                sending_spill <= '0';
            end if;
        end if;
    end process;

    rx_ready <= TX_AXI_TREADY and not will_spill;

    -- ===========================================================================
    -- Register with data that spilled over to next word due to shifting
    -- ===========================================================================
    -- spilled_tdata is just a copy of shifted_tdata, the correct bytes will be selected in the tx_logic_g for-generate.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((TX_AXI_TREADY = '1') and (rx_tvalid_reg = '1')) then
                spilled_tdata <= shifted_tdata;
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- Output register
    -- ===========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                TX_AXI_TDATA  <= slv_array_ser(tx_tdata);
                TX_AXI_TUSER  <= tx_tuser;
                TX_AXI_TKEEP  <= tx_tkeep;
                TX_AXI_TLAST  <= tx_tlast;
                TX_AXI_TVALID <= tx_tvalid;
            end if;
            if (RESET = '1') then
                TX_AXI_TVALID <= '0';
            end if;
        end if;
    end process;

end architecture;
