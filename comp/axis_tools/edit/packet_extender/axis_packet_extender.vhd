-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- AXIS_PACKET_EXTENDER extends each AXI-Stream packet by a configurable number of random bytes.
-- :vhdl:portsignal:`RX_AXI_EXT_LEN_S <AXIS_PACKET_EXTENDER.RX_AXI_EXT_LEN_S>` sets the number of
-- extension bytes at the start of the packet,
-- :vhdl:portsignal:`RX_AXI_EXT_LEN_E <AXIS_PACKET_EXTENDER.RX_AXI_EXT_LEN_E>` sets the number of
-- extension bytes at the end of the packet.
--
-- Internally, the original packet data is first extended from the start (shifted by the extension
-- length in bytes) and logic to handle spilling of the end to an extra word.
-- Then, in the next register stage, it is extended at the end by just lengthening the Keep signal
-- while also handling the spilling bytes.
--
-- .. warning::
--
--     Currently, the maximum of both extensions (separately) cannot be more than a word.
--
entity AXIS_PACKET_EXTENDER is
    generic (
        -- AXI-Stream data bus width in bits.
        AXI_TDATA_WIDTH  : natural := 512;
        -- AXI-Stream metadata bus width in bits, valid with SOP.
        AXI_TUSER_WIDTH  : natural := 11;
        -- Bit-width of extension length signal (from the packet's Start).
        -- Max extend value will be 2**EXT_LEN_S_WIDTH - 1 bytes.
        EXT_LEN_S_WIDTH  : natural := 5;
        -- Bit-width of extension length signal (from the packet's End).
        -- Max extend value will be 2**EXT_LEN_E_WIDTH - 1 bytes.
        EXT_LEN_E_WIDTH  : natural := 3
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

        -- Extension length from the packet's Start, in bytes, valid with SOP.
        RX_AXI_EXT_LEN_S : in  std_logic_vector(EXT_LEN_S_WIDTH-1 downto 0);
        -- Extension length from the packet's End, in bytes, valid with SOP.
        RX_AXI_EXT_LEN_E : in  std_logic_vector(EXT_LEN_E_WIDTH-1 downto 0);

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

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    constant DATA_BYTES   : natural := AXI_TDATA_WIDTH/8;
    constant DATA_BYTES_W : natural := log2(DATA_BYTES);

    -- Internal extend widths.
    constant EXT_LEN_S_INT_W : natural := max(EXT_LEN_S_WIDTH, DATA_BYTES_W);
    constant EXT_LEN_E_INT_W : natural := max(EXT_LEN_E_WIDTH, DATA_BYTES_W);

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    -- SOP detection / handshake
    signal rx_valid_word                  : std_logic;
    signal rx_sop                         : std_logic;
    signal rx_in_packet                   : std_logic;
    signal rx_ready                       : std_logic;

    -- Input register
    signal rx_tdata_reg                   : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal rx_tuser_reg                   : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal rx_tkeep_reg                   : std_logic_vector(DATA_BYTES-1 downto 0);
    signal rx_tlast_reg                   : std_logic;
    signal rx_tvalid_reg                  : std_logic;
    signal rx_sop_reg                     : std_logic;

    signal extend_s_len                   : unsigned(EXT_LEN_S_INT_W-1 downto 0);
    signal extend_e_len                   : unsigned(EXT_LEN_E_INT_W-1 downto 0);
    signal extend_s_len_reg               : unsigned(EXT_LEN_S_INT_W-1 downto 0);
    signal extend_e_len_reg               : unsigned(EXT_LEN_E_INT_W-1 downto 0);

    -- Barrel shifter signals
    signal ext_s_bs_din                   : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal ext_s_bs_dout                  : std_logic_vector(AXI_TDATA_WIDTH-1 downto 0);
    signal ext_s_bs_shift                 : std_logic_vector(DATA_BYTES_W-1 downto 0);

    -- Signals for packet extension from the Start
    signal ext_s_tkeep_ones_extended      : unsigned(DATA_BYTES_W+1-1 downto 0);
    signal ext_s_tkeep_ones_spilled       : unsigned(DATA_BYTES_W-1 downto 0);
    signal ext_s_will_spill               : std_logic;
    signal ext_s_sending_spill            : std_logic;
    signal ext_s_spilled_tdata            : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal ext_s_shifted_tdata            : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);

    signal ext_s_byte_ptr                 : integer range 0 to DATA_BYTES-1;
    signal ext_s_keep_ptr                 : integer range 0 to 2*DATA_BYTES-1;

    -- Packets extended from the Start
    signal ext_s_tdata                    : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal ext_s_tuser                    : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal ext_s_tkeep                    : std_logic_vector(DATA_BYTES-1 downto 0);
    signal ext_s_tlast                    : std_logic;
    signal ext_s_tvalid                   : std_logic;

    signal ext_s_tdata_reg2               : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal ext_s_tuser_reg2               : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal ext_s_tkeep_reg2               : std_logic_vector(DATA_BYTES-1 downto 0);
    signal ext_s_tlast_reg2               : std_logic;
    signal ext_s_tvalid_reg2              : std_logic;
    signal extend_e_len_reg2              : unsigned(EXT_LEN_E_INT_W-1 downto 0);

    signal ext_s_ready                    : std_logic;

    -- Signals for packet extension from the End
    signal ext_e_tkeep_ones_reg2          : integer range 0 to DATA_BYTES;
    signal ext_e_tkeep_ones_extended_reg2 : unsigned(DATA_BYTES_W+1-1 downto 0);
    signal ext_e_tkeep_ones_spilled       : unsigned(DATA_BYTES_W-1 downto 0);
    signal ext_e_will_spill               : std_logic;
    signal ext_e_sending_spill            : std_logic;
    signal ext_e_keep_ptr                 : integer range 0 to 2*DATA_BYTES-1;

    -- Packets extended from the End
    signal ext_e_tdata                    : slv_array_t(DATA_BYTES-1 downto 0)(8-1 downto 0);
    signal ext_e_tuser                    : std_logic_vector(AXI_TUSER_WIDTH-1 downto 0);
    signal ext_e_tkeep                    : std_logic_vector(DATA_BYTES-1 downto 0);
    signal ext_e_tlast                    : std_logic;
    signal ext_e_tvalid                   : std_logic;

begin

    assert EXT_LEN_S_WIDTH < DATA_BYTES_W
        report "AXIS_PACKET_EXTENDER: Extend length (form the Start) set too high! Cannot extend by more bytes than are in a single dataword."
        severity Failure;

    assert EXT_LEN_E_WIDTH < DATA_BYTES_W
        report "AXIS_PACKET_EXTENDER: Extend length (form the End) set too high! Cannot extend by more bytes than are in a single dataword."
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

                rx_sop_reg    <= rx_sop;
            end if;
            if (RESET = '1') then
                rx_tvalid_reg <= '0';
                rx_sop_reg    <= '0';
            end if;
        end if;
    end process;

    -- Extend length sampled at Start-Of-Packet.
    extend_s_len <= resize(unsigned(RX_AXI_EXT_LEN_S), EXT_LEN_S_INT_W) when (rx_sop = '1') else extend_s_len_reg;
    extend_e_len <= resize(unsigned(RX_AXI_EXT_LEN_E), EXT_LEN_E_INT_W) when (rx_sop = '1') else extend_e_len_reg;
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (rx_ready = '1') then
                extend_s_len_reg          <= extend_s_len;
                ext_s_tkeep_ones_extended <= to_unsigned(count_ones(RX_AXI_TKEEP), DATA_BYTES_W+1) + resize(extend_s_len, DATA_BYTES_W+1) - 1;
                extend_e_len_reg          <= extend_e_len;
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- Extend start logic
    -- ===========================================================================

    ext_s_bs_din   <= slv_array_ser(rx_tdata_reg);
    ext_s_bs_shift <= std_logic_vector(resize(extend_s_len_reg, DATA_BYTES_W));

    -- Shift data from the RX reg
    rx1_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        BLOCKS     => DATA_BYTES,
        BLOCK_SIZE => 8,
        SHIFT_LEFT => true
    )
    port map (
        DATA_IN  => ext_s_bs_din,
        DATA_OUT => ext_s_bs_dout,
        SEL      => ext_s_bs_shift
    );

    ext_s_shifted_tdata <= slv_array_deser(ext_s_bs_dout, DATA_BYTES);

    -- Boundary where the extension data ends and the packet data begins.
    ext_s_byte_ptr <= to_integer(resize(extend_s_len_reg, DATA_BYTES_W));
    -- Boundary where the (shifted) packet ends within the word.
    ext_s_keep_ptr <= to_integer(ext_s_tkeep_ones_spilled) when (ext_s_sending_spill = '1') else to_integer(ext_s_tkeep_ones_extended);

    -- The last word will spill into one extra word after sifting.
    ext_s_will_spill <= rx_tlast_reg and rx_tvalid_reg and          -- There is a valid tlast and
                        ext_s_tkeep_ones_extended(DATA_BYTES_W) and -- the number of valid bytes + extension bytes go over the dataword's capacity.
                        not ext_s_sending_spill;                    -- Reset after the spill part is sent.

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (ext_s_ready = '1') then
                ext_s_sending_spill      <= ext_s_will_spill;
                ext_s_tkeep_ones_spilled <= ext_s_tkeep_ones_extended(DATA_BYTES_W-1 downto 0);
            end if;
            if (RESET = '1') then
                ext_s_sending_spill <= '0';
            end if;
        end if;
    end process;

    rx_ready <= ext_s_ready and not ext_s_will_spill;

    -- ---------------------------------------------------------------------------
    -- Register with data that spilled over to next word due to shifting
    -- ---------------------------------------------------------------------------
    -- spilled_tdata is just a copy of shifted_tdata, the correct bytes will be selected in the tx_logic_g for-generate.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((ext_s_ready = '1') and (rx_tvalid_reg = '1')) then
                ext_s_spilled_tdata <= ext_s_shifted_tdata;
            end if;
        end if;
    end process;

    -- ---------------------------------------------------------------------------
    -- Extend start data finalization
    -- ---------------------------------------------------------------------------
    ext_s_logic_g : for db in 0 to DATA_BYTES-1 generate
        ext_s_tdata(db) <= ext_s_spilled_tdata(db) when (db < ext_s_byte_ptr) else ext_s_shifted_tdata(db);
        ext_s_tkeep(db) <= '1'                     when (db <= ext_s_keep_ptr) else '0';
    end generate;
    ext_s_tuser  <= rx_tuser_reg;
    ext_s_tlast  <= (rx_tlast_reg and not ext_s_will_spill) or ext_s_sending_spill;
    ext_s_tvalid <= rx_tvalid_reg or ext_s_sending_spill;

    -- ===========================================================================
    -- Mid-stage register
    -- ===========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (ext_s_ready = '1') then
                ext_s_tdata_reg2  <= ext_s_tdata;
                ext_s_tuser_reg2  <= ext_s_tuser;
                ext_s_tkeep_reg2  <= ext_s_tkeep;
                ext_s_tlast_reg2  <= ext_s_tlast;
                ext_s_tvalid_reg2 <= ext_s_tvalid;

                extend_e_len_reg2 <= extend_e_len_reg;
            end if;
            if (RESET = '1') then
                ext_s_tvalid_reg2 <= '0';
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- Extend end logic
    -- ===========================================================================

    ext_e_tkeep_ones_reg2          <= count_ones(ext_s_tkeep_reg2);
    ext_e_tkeep_ones_extended_reg2 <= to_unsigned(ext_e_tkeep_ones_reg2, DATA_BYTES_W+1) + resize(extend_e_len_reg2, DATA_BYTES_W+1) - 1;
    ext_e_will_spill               <= ext_s_tlast_reg2 and ext_s_tvalid_reg2 and
                                      ext_e_tkeep_ones_extended_reg2(DATA_BYTES_W) and
                                      not ext_e_sending_spill;

    -- Boundary where the extended packet will end. No byte_ptr is needed.
    ext_e_keep_ptr <= to_integer(ext_e_tkeep_ones_spilled) when (ext_e_sending_spill = '1') else to_integer(ext_e_tkeep_ones_extended_reg2);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                ext_e_sending_spill      <= ext_e_will_spill;
                ext_e_tkeep_ones_spilled <= ext_e_tkeep_ones_extended_reg2(DATA_BYTES_W-1 downto 0);
            end if;
            if (RESET = '1') then
                ext_e_sending_spill <= '0';
            end if;
        end if;
    end process;

    ext_s_ready <= TX_AXI_TREADY and not ext_e_will_spill;

    -- ---------------------------------------------------------------------------
    -- Extend end data finalization
    -- ---------------------------------------------------------------------------
    ext_e_tdata  <= ext_s_tdata_reg2;
    ext_e_tuser  <= ext_s_tuser_reg2;
    ext_e_logic_g : for db in 0 to DATA_BYTES-1 generate
        ext_e_tkeep(db) <= '1' when (db <= ext_e_keep_ptr) else '0';
    end generate;
    ext_e_tlast  <= (ext_s_tlast_reg2 and not ext_e_will_spill) or ext_e_sending_spill;
    ext_e_tvalid <= ext_s_tvalid_reg2 or ext_e_sending_spill;

    -- ===========================================================================
    -- Output register
    -- ===========================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_AXI_TREADY = '1') then
                TX_AXI_TDATA  <= slv_array_ser(ext_e_tdata);
                TX_AXI_TUSER  <= ext_e_tuser;
                TX_AXI_TKEEP  <= ext_e_tkeep;
                TX_AXI_TLAST  <= ext_e_tlast;
                TX_AXI_TVALID <= ext_e_tvalid;
            end if;
            if (RESET = '1') then
                TX_AXI_TVALID <= '0';
            end if;
        end if;
    end process;

end architecture;
