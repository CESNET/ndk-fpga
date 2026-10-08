-- dram_fifo.vhd
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Adam Zatloukal <zatloukal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;


-- FIFO logic built around an external DDR memory using the Avalon Memory-Mapped (AVMM) interface.
-- Data is written to memory one beat at a time. The first beat of each N packets
-- is the packet length metadata beat, followed by the packet payload beats.
-- Write addresses increment manually after each accepted beat.
--
entity DRAM_FIFO is
    generic (
        -- Width of AVMM_ADDRESS. Set by the card's memory controller.
        DDR_ADDR_WIDTH  : natural := 27;
        -- Width of AVMM_BURSTCOUNT. Transactions are single-beat, so the output
        -- is tied to 1.
        DDR_BURST_WIDTH : natural := 7;
        -- Width of the AVMM data path, and therefore of one ring item.
        DDR_DATA_WIDTH  : natural := 512;

        -- Width of both AXI-Stream ports.
        AXI_DATA_WIDTH : natural := 512;
        -- Depth in DDR words. Must not exceed the memory behind the AVMM port.
        FIFO_ITEMS     : natural := 2 ** 13;
        -- Largest packet in bytes (4 KB). Sets LEN_WIDTH = log2(PKT_MTU+1) and
        -- the width of TX_PKT_LEN. A frame larger than this has its stored
        -- length wrapped, which corrupts every later packet in the metaword.
        PKT_MTU        : natural := 2 ** 12;

        -- Target device string, passed to the FIFO primitives.
        DEVICE : string := "AGILEX";

        -- Depth of the on-chip write buffer. An assert checks that at least one
        -- MTU packet fits.
        FIFO_BUFF_IN_ITEMS  : natural := 2**16;
        -- Depth of the read prefetch buffer. An assert checks that at least one
        -- MTU packet fits.
        FIFO_BUFF_OUT_ITEMS : natural := 2**12
    );
    port (
        -- =======================================================================
        -- FIFO interface
        -- =======================================================================

        CLK                 : in std_logic;
        RESET               : in std_logic;

        -- =======================================================================
        -- Write interface
        -- =======================================================================

        RX_AXI_DATA         : in std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
        RX_AXI_KEEP         : in std_logic_vector(AXI_DATA_WIDTH/8 - 1 downto 0);
        RX_AXI_LAST         : in std_logic;
        RX_AXI_VALID        : in std_logic;
        RX_AXI_READY        : out std_logic;

        -- =======================================================================
        -- Read interface
        -- =======================================================================

        TX_AXI_DATA         : out std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
        TX_AXI_KEEP         : out std_logic_vector(AXI_DATA_WIDTH/8 - 1 downto 0);
        TX_AXI_LAST         : out std_logic;
        TX_AXI_VALID        : out std_logic;
        TX_AXI_READY        : in std_logic;

        -- Packet length output, valid with first payload beat (TX_AXI_VALID=1 and SOF)
        TX_PKT_LEN          : out std_logic_vector(log2(PKT_MTU+1)-1 downto 0);

        -- =======================================================================
        -- DRAM interface
        -- =======================================================================

        -- Request interface
        AVMM_ADDRESS       : out std_logic_vector(DDR_ADDR_WIDTH - 1 downto 0);
        AVMM_BURSTCOUNT    : out std_logic_vector(DDR_BURST_WIDTH - 1 downto 0);
        AVMM_WRITE         : out std_logic;
        AVMM_WRITEDATA     : out std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);
        AVMM_READ          : out std_logic;
        AVMM_READY         : in  std_logic;

        -- Response interface
        AVMM_READDATA      : in  std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);
        AVMM_READDATAVALID : in  std_logic;

        -- Low when another word of FIFO_ITEMS b can be written.
        DDR_FULL           : out std_logic;
        -- Set by user - when high reading via the AVMM_* interface is enabled
        DDR_READ_EN        : in  std_logic
    );
end entity;

architecture FULL of DRAM_FIFO is
    constant ADDR_WIDTH : natural := log2(FIFO_ITEMS);  -- width of DDR read/write ptr address space
    constant PTR_WIDTH  : natural := ADDR_WIDTH + 1;    --  +1 is the WRAP bit. Rest is address


    constant LEN_WIDTH          : natural := log2(PKT_MTU + 1);                                             -- width of one pkt_len
    constant META_LEN_COUNT_MAX : natural := DDR_DATA_WIDTH / LEN_WIDTH;                                    -- max lengths if the whole word were used, no count field (512/13 = 39)
    constant META_COUNT_BITS    : natural := log2(META_LEN_COUNT_MAX + 1);                                  -- how many pkt_lens are valid within a metaword (6b)
    constant META_LEN_COUNT     : natural := (DDR_DATA_WIDTH - META_COUNT_BITS) / LEN_WIDTH;                -- pkt_len fit into one metadata word (38)
    constant META_COUNT_W       : natural := log2(META_LEN_COUNT + 1);                                      -- width of internal counter
    constant META_UNUSED_BITS   : natural := DDR_DATA_WIDTH - META_COUNT_BITS - META_LEN_COUNT * LEN_WIDTH; -- leftover high bits (12)

    constant META_FIFO_ITEMS        : natural := 2**10;

    constant FLUSH_TIMEOUT : natural := 1024;


    --  DDR read/write addressing interface
    signal write_ptr        : unsigned(PTR_WIDTH - 1 downto 0) := (others => '0');
    signal read_ptr         : unsigned(PTR_WIDTH - 1 downto 0) := (others => '0');
    signal diff             : unsigned(PTR_WIDTH - 1 downto 0);     -- write_ptr - read_ptr
    signal can_read         : std_logic;                            -- based on diff
    signal can_write        : std_logic;                            -- based on diff
    signal inc_read_ptr     : std_logic;
    signal inc_write_ptr    : std_logic;

    signal write_wants  : std_logic;                                -- request a write. evaluated by the arbitrator
    signal read_wants   : std_logic;                                -- request a read. evaluated by the arbitrator

    --  AVMM interface signals

    signal avmm_write_req       : std_logic;                            -- directly asserts AVMM_WRITE
    signal avmm_read_req        : std_logic;                            -- directly asserts AVMM_READ
    signal avmm_rd_addr         : std_logic_vector(DDR_ADDR_WIDTH - 1 downto 0);
    signal avmm_wr_addr         : std_logic_vector(DDR_ADDR_WIDTH - 1 downto 0);

    --  Packed metadata FIFO
    signal meta_fifo_di    : std_logic_vector(DDR_DATA_WIDTH-1 downto 0);
    signal meta_fifo_wr    : std_logic;
    signal meta_fifo_do    : std_logic_vector(DDR_DATA_WIDTH-1 downto 0);
    signal meta_fifo_rd    : std_logic;
    signal meta_fifo_empty : std_logic;
    signal meta_fifo_full  : std_logic;
    signal meta_fifo_afull : std_logic;

    --  Output from packet_len
    signal plen_fifo_tdata  : std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
    signal plen_fifo_tlast  : std_logic;
    signal plen_fifo_tkeep  : std_logic_vector(AXI_DATA_WIDTH/8 - 1 downto 0);
    signal plen_fifo_tready : std_logic;
    signal plen_fifo_tvalid : std_logic;
    signal fifo_in_ready    : std_logic;

    signal new_pkt_len : std_logic;

    --  Output from fifo_buffer_in
    signal fifo_tdata  : std_logic_vector(AXI_DATA_WIDTH - 1 downto 0);
    signal fifo_tlast  : std_logic;
    signal fifo_tkeep  : std_logic_vector(AXI_DATA_WIDTH/8 - 1 downto 0);
    signal fifo_tready : std_logic;
    signal fifo_tvalid : std_logic;

    --  Length packing
    signal pkt_buffered         : std_logic;                                          -- asserted when both metaword and fifo_buffer_in contain valid data
    signal metaword_sent        : std_logic;
    signal metaword_sent_next   : std_logic;
    signal pkt_len_val          : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);

    signal meta_slot_cnt     : unsigned(META_COUNT_W - 1 downto 0);                         -- how many slots are currently filled
    signal meta_word         : std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);               -- memory map: [ PADDING (12b) | COUNT (6b) | P37 (13b) | ... | P0 ]
    signal meta_word_full    : std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);
    signal meta_word_flush   : std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);
    signal meta_word_valid   : std_logic;
    signal meta_word_ready   : std_logic;

    signal meta_word_next         : std_logic_vector(DDR_DATA_WIDTH - 1 downto 0);
    signal meta_word_valid_next   : std_logic;
    signal meta_shift_en          : std_logic;

    type   meta_len_array_t is array (META_LEN_COUNT downto 0) of std_logic_vector(LEN_WIDTH-1 downto 0);
    signal meta_len_shreg : meta_len_array_t;

    signal meta_lens_packed : std_logic_vector(META_LEN_COUNT * LEN_WIDTH - 1 downto 0);
    signal meta_lens_flush  : std_logic_vector(META_LEN_COUNT * LEN_WIDTH - 1 downto 0);

    signal flush_timer       : unsigned(log2(FLUSH_TIMEOUT + 1) - 1 downto 0);
    signal meta_flush        : std_logic;           -- force an output of a partial word
    signal meta_flush_cond   : std_logic;           -- raw combinational condition for flushing a partial word
    signal meta_flush_req    : std_logic;           -- combinational request to flush a partial word
    signal inc_flush_timer   : std_logic;
    signal reset_flush_timer : std_logic;

    --  Read side FSM
    type   fmt_state_t is (FMT_META, FMT_PAYLOAD);
    signal fmt_state                     : fmt_state_t;
    signal fmt_remaining                 : unsigned(log2(PKT_MTU+1)-1 downto 0);                         -- bytes remaining to read from pkt
    signal fmt_pkt_idx                   : unsigned(META_COUNT_W - 1 downto 0);                          -- index of pkt to be read
    signal fmt_pkts_remaining            : unsigned(META_COUNT_W - 1 downto 0);                          -- num of pkts remaining to read, based on metaword
    signal fmt_pkt_lens                  : std_logic_vector(META_LEN_COUNT * LEN_WIDTH - 1 downto 0);    -- extracted from metaword. contains lengths of pkts

    signal fmt_state_next                : fmt_state_t;
    signal fmt_remaining_next            : unsigned(log2(PKT_MTU+1)-1 downto 0);
    signal fmt_pkt_idx_next              : unsigned(META_COUNT_W - 1 downto 0);
    signal fmt_pkts_remaining_next       : unsigned(META_COUNT_W - 1 downto 0);
    signal fmt_pkt_lens_next             : std_logic_vector(META_LEN_COUNT * LEN_WIDTH - 1 downto 0);

    signal fmt_pkt_len_current           : unsigned(log2(PKT_MTU+1)-1 downto 0);
    signal fmt_pkt_len_current_next      : unsigned(log2(PKT_MTU+1)-1 downto 0);

    signal pkt_written_cnt  : unsigned(META_COUNT_W - 1 downto 0);      -- num of pkts from metaword written to DDR
    signal meta_pkt_count   : unsigned(META_COUNT_W - 1 downto 0);      -- num of valid pkts extracted from metaword

    signal write_data_valid : std_logic;

    signal out_fifo_do      : std_logic_vector(DDR_DATA_WIDTH-1 downto 0);
    signal out_fifo_rd      : std_logic;
    signal out_fifo_empty   : std_logic;

    signal outstanding_read_cnt : unsigned(log2(FIFO_BUFF_OUT_ITEMS) downto 0);
    signal out_fifo_credits     : unsigned(log2(FIFO_BUFF_OUT_ITEMS) downto 0);

    signal grant_write      : std_logic;
    signal grant_read       : std_logic;
    signal req_lock         : std_logic;
    signal lock_is_write    : std_logic;


    function ones_mask (len : unsigned) return std_logic_vector is
    begin
        if (len >= AXI_DATA_WIDTH/8) then
            return (AXI_DATA_WIDTH/8-1 downto 0 => '1');
        else
            return std_logic_vector(
                resize(
                    unsigned'(shift_left(to_unsigned(1, AXI_DATA_WIDTH/8), to_integer(len))-1),
                        AXI_DATA_WIDTH/8
                )
            );
        end if;
    end function;

    function get_pkt_len (lens : std_logic_vector(META_LEN_COUNT * LEN_WIDTH - 1 downto 0);
        idx  : unsigned(META_COUNT_BITS - 1 downto 0)
    ) return unsigned is
    begin
        return unsigned(
            lens(
                (to_integer(idx) + 1) * LEN_WIDTH - 1 downto
                to_integer(idx) * LEN_WIDTH
            )
        );
    end function;

    function get_pkts_remaining (metaword : std_logic_vector(DDR_DATA_WIDTH-1 downto 0))
    return unsigned is
    begin
        return unsigned(metaword(
                    DDR_DATA_WIDTH-META_UNUSED_BITS-1 downto
                    DDR_DATA_WIDTH-META_UNUSED_BITS-META_COUNT_BITS
                ));
    end function;

    function get_pkt_lens (metaword : std_logic_vector(DDR_DATA_WIDTH-1 downto 0))
    return std_logic_vector is
    begin
        return std_logic_vector(metaword(
                    DDR_DATA_WIDTH-META_UNUSED_BITS-META_COUNT_BITS-1 downto
                    0
                ));
    end function;

    function get_addr (ptr : unsigned(PTR_WIDTH - 1 downto 0))
    return std_logic_vector is
    begin
        return std_logic_vector(
                resize(
                    ptr(ADDR_WIDTH-1 downto 0), DDR_ADDR_WIDTH
                )
            );
    end function;
begin
    assert AXI_DATA_WIDTH = DDR_DATA_WIDTH
        report "AXI_DATA_WIDTH (" & integer'image(AXI_DATA_WIDTH) &
               ") must equal DDR_DATA_WIDTH (" & integer'image(DDR_DATA_WIDTH) & ")"
        severity failure;

    -- read_ptr/write_ptr wrap naturally only when FIFO_ITEMS is a power of two.
    assert 2**log2(FIFO_ITEMS) = FIFO_ITEMS
        report "FIFO_ITEMS (" & integer'image(FIFO_ITEMS) &
               ") must be a power of two"
        severity failure;

    assert log2(FIFO_ITEMS) <= DDR_ADDR_WIDTH
        report "FIFO_ITEMS (" & integer'image(FIFO_ITEMS) &
               ") needs " & integer'image(log2(FIFO_ITEMS)) &
               " address bits, but DDR_ADDR_WIDTH is " & integer'image(DDR_ADDR_WIDTH)
        severity failure;

    assert FIFO_BUFF_IN_ITEMS >= PKT_MTU/(AXI_DATA_WIDTH/8)
        report "FIFO_BUFF_IN_ITEMS (" & integer'image(FIFO_BUFF_IN_ITEMS) &
               ") must hold at least one MTU packet (" &
               integer'image(PKT_MTU/(AXI_DATA_WIDTH/8)) & " items)"
        severity failure;

    assert FIFO_BUFF_OUT_ITEMS >= PKT_MTU/(AXI_DATA_WIDTH/8)
        report "FIFO_BUFF_OUT_ITEMS (" & integer'image(FIFO_BUFF_OUT_ITEMS) &
               ") must hold at least one MTU packet (" &
               integer'image(PKT_MTU/(AXI_DATA_WIDTH/8)) & " items)"
        severity failure;

    -- =======================================================================
    -- Input buffers (data & metadata)
    -- =======================================================================

    packet_len: entity work.AXIS_PACKET_LEN
    generic map (
        AXI_TDATA_WIDTH     => AXI_DATA_WIDTH,
        PKT_MTU             => PKT_MTU,
        DEVICE              => DEVICE
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        -- RX
        RX_AXI_TDATA    => RX_AXI_DATA,
        RX_AXI_TKEEP    => RX_AXI_KEEP,
        RX_AXI_TLAST    => RX_AXI_LAST,
        RX_AXI_TVALID   => RX_AXI_VALID,
        RX_AXI_TREADY   => RX_AXI_READY,

        -- TX
        TX_AXI_TDATA    => plen_fifo_tdata,
        TX_AXI_TKEEP    => plen_fifo_tkeep,
        TX_AXI_TLAST    => plen_fifo_tlast,
        TX_AXI_TVALID   => plen_fifo_tvalid,
        TX_AXI_TREADY   => plen_fifo_tready,

        TX_PACKET_LEN   => pkt_len_val
    );

    fifo_buffer_in: entity work.AXIS_FIFO
    generic map (
        AXI_TDATA_WIDTH     => AXI_DATA_WIDTH,
        AXI_TUSER_WIDTH     => 0,                           -- not used
        ITEMS               => FIFO_BUFF_IN_ITEMS,
        FAKE_FIFO           => false,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        FIFO_TYPE           => 1

    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        -- RX
        RX_AXI_TDATA    => plen_fifo_tdata,
        RX_AXI_TKEEP    => plen_fifo_tkeep,
        RX_AXI_TLAST    => plen_fifo_tlast,
        RX_AXI_TVALID   => plen_fifo_tvalid and plen_fifo_tready,
        RX_AXI_TREADY   => fifo_in_ready,

        -- TX
        TX_AXI_TDATA    => fifo_tdata,
        TX_AXI_TKEEP    => fifo_tkeep,
        TX_AXI_TLAST    => fifo_tlast,
        TX_AXI_TVALID   => fifo_tvalid,
        TX_AXI_TREADY   => fifo_tready,

        FULL            => open,
        AFULL           => open,
        STATUS          => open,
        EMPTY           => open,
        AEMPTY          => open
    );

    -- Backpressure from the packer to AXIS_PACKET_LEN / fifo_buffer_in.
    -- RX must stall if the metadata FIFO is almost full, otherwise lengths could
    -- be lost. The payload path uses the same ready because lengths are produced
    -- on the last payload beat.
    plen_fifo_tready <= fifo_in_ready and not meta_fifo_afull;

    -- Packed metadata FIFO: stores metadata words (valid count + up to 38 lengths).
    -- Pushed when a metadata word is complete or flushed.
    -- Popped when the write controller emits a metadata beat.
    meta_fifo: entity work.FIFOX
    generic map (
        DATA_WIDTH          => DDR_DATA_WIDTH,
        ITEMS               => META_FIFO_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 0,
        FAKE_FIFO           => false
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        -- Write interface
        DI     => meta_fifo_di,
        WR     => meta_fifo_wr,
        FULL   => meta_fifo_full,
        AFULL  => meta_fifo_afull,
        STATUS => open,

        -- Read interface
        DO     => meta_fifo_do,
        RD     => meta_fifo_rd,
        EMPTY  => meta_fifo_empty,
        AEMPTY => open
    );

    -- =======================================================================
    -- Metaword packing
    -- =======================================================================

    -- Packed metaword memory map:
    new_pkt_len <= '1' when plen_fifo_tready = '1' and
                            plen_fifo_tvalid = '1' and
                            plen_fifo_tlast = '1'  else
                            '0';

    process (CLK)
    begin
        if (rising_edge (CLK)) then
            if (RESET = '1') then
                meta_word       <= (others => '0');
                meta_word_valid <= '0';
            elsif (meta_word_valid = '0' or meta_word_ready = '1') then
                meta_word       <= meta_word_next;
                meta_word_valid <= meta_word_valid_next;
            end if;
        end if;
    end process;

    -- Valid lengths counter
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                meta_slot_cnt <= (others => '0');
            elsif (new_pkt_len = '1' and meta_slot_cnt = META_LEN_COUNT - 1) then
                meta_slot_cnt <= (others => '0');
            elsif (meta_flush = '1' and meta_slot_cnt > 0) then
                meta_slot_cnt <= (0 => new_pkt_len, others => '0');
            elsif (new_pkt_len = '1' and meta_slot_cnt < META_LEN_COUNT - 1) then
                meta_slot_cnt <= meta_slot_cnt + 1;
            end if;
        end if;
    end process;


    -- Shift register
    meta_shift_en <= '1' when new_pkt_len = '1' and (meta_slot_cnt < META_LEN_COUNT) else
                        '0';

    -- lengths are stored in idx 1 (latest len) - 38 (oldest len)
    meta_len_shreg(0) <= pkt_len_val;
    meta_len_shreg_g : for s in 0 to META_LEN_COUNT-1 generate
        process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (meta_shift_en = '1') then
                    meta_len_shreg(s+1) <= meta_len_shreg(s);
                end if;
            end if;
        end process;
    end generate;

    -- Packing from shift register into a vector
    -- Full word
    process (all)
    begin
        for i in 0 to META_LEN_COUNT - 1 loop
            if (i = META_LEN_COUNT - 1) then
                meta_lens_packed((i + 1) * LEN_WIDTH - 1 downto i * LEN_WIDTH)
                    <= pkt_len_val;
            else
                meta_lens_packed((i + 1) * LEN_WIDTH - 1 downto i * LEN_WIDTH)
                    <= meta_len_shreg(META_LEN_COUNT - 1 - i);
            end if;
        end loop;
    end process;

    -- Partial word
    process (all)
    begin
        for i in 0 to META_LEN_COUNT - 1 loop
            if (i < to_integer(meta_slot_cnt)) then
                meta_lens_flush((i + 1) * LEN_WIDTH - 1 downto i * LEN_WIDTH)
                    <= meta_len_shreg(to_integer(meta_slot_cnt) - i);
            else
                meta_lens_flush((i + 1) * LEN_WIDTH - 1 downto i * LEN_WIDTH)
                    <= (others => '0');
            end if;
        end loop;
    end process;


    -- Packing full metaword
    -- Full word (PKT_MTU = 4096)
    -- [ PADDING (12b) | COUNT (6b) | P37 (13b) (latest)| P36 (13b) | ... | P1 (13b) | P0 (13b) (oldest)]
    meta_word_full <= std_logic_vector(
                                       to_unsigned(0, META_UNUSED_BITS)
                                   ) & std_logic_vector(
                                                              to_unsigned(META_LEN_COUNT, META_COUNT_BITS)
                                                          ) & meta_lens_packed;

    -- Partial word
    -- [ PADDING (12b) | COUNT (6b) | PADDING  | Pn (13b) | ... | P1 | P0]
    meta_word_flush <= std_logic_vector(
                                        to_unsigned(0, META_UNUSED_BITS)
                                    ) & std_logic_vector(
                                                               to_unsigned(to_integer(meta_slot_cnt), META_COUNT_BITS)
                                                           ) & meta_lens_flush;


    meta_word_next <= meta_word_full when (meta_slot_cnt = META_LEN_COUNT - 1 and new_pkt_len = '1') else
                                  meta_word_flush;

    meta_word_valid_next <= '1' when (meta_slot_cnt = META_LEN_COUNT - 1 and new_pkt_len = '1') or
                                    (meta_flush = '1' and meta_slot_cnt > 0) else
                                '0';


    -- Flush timeout counter
    -- After n clock cycles of not receiving a new packet length
    -- meta_flush is asserted resulting in saving partial word into meta_fifo
    inc_flush_timer <= '1' when (meta_slot_cnt > 0)  and
                                new_pkt_len = '0'    and
                                (flush_timer < FLUSH_TIMEOUT) else
                            '0';

    -- Raw combinational condition that indicates a partial metadata word should
    -- be flushed.  It is used for both reset_flush_timer and meta_flush_req,
    -- but reset_flush_timer must not depend on meta_flush_req (or meta_flush)
    -- in order to avoid a combinational loop.
    meta_flush_cond <= '1' when flush_timer >= FLUSH_TIMEOUT and meta_slot_cnt /= 0 and
                            (meta_word_valid = '0' or meta_word_ready = '1') else
                        '0';

    -- The flush request is suppressed only when a new packet length arrives in
    -- the same cycle (so a full metaword is produced instead of a partial flush).
    -- It is NOT suppressed by the flush itself, otherwise meta_flush would never fire.
    meta_flush_req <= '1' when meta_flush_cond = '1' and
                                not (plen_fifo_tvalid = '1' and plen_fifo_tready = '1' and plen_fifo_tlast = '1') else
                          '0';

    reset_flush_timer <= '1' when (plen_fifo_tvalid = '1' and plen_fifo_tready = '1' and plen_fifo_tlast = '1') or         -- valid pkt_len was saved
                                meta_flush_cond = '1' else                                                                 -- partial word was flushed -> reset the timer
                        '0';

    -- Registered flush pulse: asserted for one cycle when the flush condition is met.
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                meta_flush <= '0';
            else
                meta_flush <= meta_flush_req;
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1'  or reset_flush_timer = '1') then
                flush_timer <= (others => '0');
            elsif (inc_flush_timer = '1') then
                flush_timer <= flush_timer + 1;
            end if;
        end if;
    end process;

    -- The output of the packer is ready whenever the metadata FIFO is not full.
    meta_word_ready <= not meta_fifo_full;

    -- Write assembled metadata word into FIFO when valid and FIFO can accept.
    meta_fifo_di <= meta_word;
    meta_fifo_wr <= meta_word_valid and meta_word_ready;

    -- A packet is ready to write when both the data FIFO has a full packet (implied by meta_fifo_empty = '0')
    -- AND the packed metadata FIFO has a corresponding metadata word queued.
    pkt_buffered <= '1' when meta_fifo_empty = '0' or metaword_sent = '1' else '0';

    -- =======================================================================
    -- Reading from fifo_buffer_in & writing to DDR
    -- =======================================================================

    -- Pop the metaword one cycle after its beat is accepted. Safe because every
    -- metaword carries >= 1 packet of >= 1 beat(s), so the next metaword cannot be
    -- accepted before the pop takes effect.
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                meta_fifo_rd <= '0';
            else
                meta_fifo_rd <= AVMM_WRITE and AVMM_READY and (not metaword_sent);
            end if;
        end if;
    end process;


    -- metadata word sent flag
    -- '0' -> next write is the metadata beat (packed lengths from meta_fifo_do)
    -- '1' -> next write(s) are payload beats from fifo_buffer_in
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                metaword_sent <= '0';
            else
                metaword_sent <= metaword_sent_next;
            end if;
        end if;
    end process;

    process (all)
    begin
        metaword_sent_next <= metaword_sent;

        if (AVMM_READY = '1' and AVMM_WRITE = '1') then
            if (metaword_sent = '0') then
                metaword_sent_next <= '1';
            elsif (fifo_tvalid = '1' and fifo_tlast = '1' and fifo_tready = '1' and
                   pkt_written_cnt = meta_pkt_count - 1 and
                   meta_pkt_count /= 0) then
                metaword_sent_next <= '0';
            end if;
        end if;
    end process;

    -- When metaword is read from fifo save its length into a register
    -- for comparison
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                meta_pkt_count <= (others => '0');
            elsif (AVMM_WRITE = '1' and AVMM_READY = '1' and metaword_sent = '0') then
                meta_pkt_count <= get_pkts_remaining(AVMM_WRITEDATA);
            end if;
        end if;
    end process;

    -- pkt_written_cnt: packets of the current metaword already written to DDR
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pkt_written_cnt <= (others => '0');
            elsif (AVMM_WRITE = '1' and AVMM_READY = '1') then
                if (metaword_sent = '0') then
                    pkt_written_cnt <= (others => '0');          -- metaword accepted
                elsif (fifo_tvalid = '1' and fifo_tlast = '1') then
                    pkt_written_cnt <= pkt_written_cnt + 1;      -- packet finished
                end if;
            end if;
        end if;
    end process;

    -- Calculate diff, set can_read & can_write
    diff        <= write_ptr - read_ptr;
    can_write   <= '1' when diff < (FIFO_ITEMS - 1) else '0';
    can_read    <= '1' when diff > 0 else '0';

    DDR_FULL <= not can_write;

    -- Can we increment a pointer?
    inc_write_ptr   <= AVMM_WRITE and AVMM_READY;
    inc_read_ptr    <= AVMM_READ and AVMM_READY;

    -- read_ptr/write_ptr counter
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                read_ptr  <= (others => '0');
                write_ptr <= (others => '0');
            else
                if (inc_read_ptr) then
                    read_ptr <= read_ptr + 1;
                end if;
                if (inc_write_ptr) then
                    write_ptr <= write_ptr + 1;
                end if;
            end if;
        end if;
    end process;

    -- Outstanding reads counter
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                outstanding_read_cnt <= (others => '0');
            else
                if (AVMM_READY = '1' and AVMM_READ = '1' and AVMM_READDATAVALID = '0') then
                    outstanding_read_cnt <= outstanding_read_cnt + 1;
                elsif (AVMM_READDATAVALID = '1' and not (AVMM_READY = '1' and AVMM_READ = '1')) then
                    outstanding_read_cnt <= outstanding_read_cnt - 1;
                end if;
            end if;
        end if;
    end process;

    -- Credit counter: tracks free slots in out_fifo.
    -- Decremented when a read is issued (a beat will eventually arrive).
    -- Incremented when a beat is popped from out_fifo.
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                out_fifo_credits <= to_unsigned(FIFO_BUFF_OUT_ITEMS, out_fifo_credits'length);
            else
                if (not (AVMM_READY = '1' and AVMM_READ = '1' and out_fifo_rd = '1')) then
                    if (AVMM_READY = '1' and AVMM_READ = '1') then
                        out_fifo_credits <= out_fifo_credits - 1;
                    end if;
                    if (out_fifo_rd = '1') then
                        out_fifo_credits <= out_fifo_credits + 1;
                    end if;
                end if;
            end if;
        end if;
    end process;


    -- =======================================================================
    -- AVMM r/w arbitration
    -- =======================================================================


    -- Write condition
    write_wants <= '1' when pkt_buffered = '1' and
                        can_write = '1' and
                        write_data_valid = '1' else
                        '0';

    grant_write <= lock_is_write        when req_lock = '1' else write_wants;
    grant_read  <= not lock_is_write    when req_lock = '1' else read_wants and not write_wants;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                req_lock <= '0';
            else
                req_lock <= (grant_write or grant_read) and not AVMM_READY;
                if (req_lock = '0') then
                    lock_is_write <= grant_write;
                end if;
            end if;
        end if;
    end process;

    avmm_write_req <= grant_write;
    avmm_read_req  <= grant_read;


    -- =======================================================================
    -- AVMM interface
    -- =======================================================================

    -- calculate read/write address
    avmm_wr_addr <= get_addr(write_ptr);
    avmm_rd_addr <= get_addr(read_ptr);

    -- A write beat carries valid data only when there is a metaword to send
    -- (metaword_sent='0' and the metadata FIFO is non-empty) or a payload beat
    -- is present (metaword_sent='1' and the payload FIFO has valid data).
    write_data_valid <= (not metaword_sent and not meta_fifo_empty) or
                        (metaword_sent and fifo_tvalid);

    -- set avmm interface signals (single-beat transactions)
    AVMM_ADDRESS    <= avmm_rd_addr when avmm_read_req = '1' else
                       avmm_wr_addr;

    -- not currently used
    AVMM_BURSTCOUNT <= std_logic_vector(to_unsigned(1, DDR_BURST_WIDTH));

    AVMM_WRITE      <= avmm_write_req and write_data_valid;
    AVMM_WRITEDATA  <= meta_fifo_do when metaword_sent = '0' else fifo_tdata;
    AVMM_READ       <= avmm_read_req;

    -- Pop the FIFO only during payload beats (not during the metadata beat)
    fifo_tready     <= avmm_write_req and AVMM_READY when metaword_sent = '1' else '0';

    -- =======================================================================
    -- Output FIFO buffer
    -- =======================================================================

    -- Prefetch payload from DDR into fifo_buffer_out.
    -- Use credit counter to prevent overflow and silent discard of read data.
    -- The credit counter is updated in the same cycle as the read issuance,
    -- so it has no registered-delay problem.
    read_wants <= '1' when (diff > outstanding_read_cnt) and                                          -- Dont read when there is nothing in DRAM
                           (out_fifo_credits > 1) and
                            DDR_READ_EN = '1' else
                      '0';

    fifo_buffer_out: entity work.FIFOX
    generic map (
        DATA_WIDTH          => DDR_DATA_WIDTH,
        ITEMS               => FIFO_BUFF_OUT_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 0,
        FAKE_FIFO           => false
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        -- Write interface
        DI     => AVMM_READDATA,
        WR     => AVMM_READDATAVALID,
        FULL   => open,
        AFULL  => open,
        STATUS => open,

        -- Read interface
        DO     => out_fifo_do,
        RD     => out_fifo_rd,
        EMPTY  => out_fifo_empty,
        AEMPTY => open
    );

    -- =======================================================================
    -- Read FSM & AXI signal formatting
    -- =======================================================================

    -- Reconstruct TLAST and TKEEP from the stored packet length.
    fmt_present_state_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                fmt_state           <= FMT_META;
                fmt_remaining       <= (others => '0');
                fmt_pkt_idx         <= (others => '0');
                fmt_pkts_remaining  <= (others => '0');
                fmt_pkt_lens        <= (others => '0');
                fmt_pkt_len_current <= (others => '0');
            else
                fmt_state           <= fmt_state_next;
                fmt_remaining       <= fmt_remaining_next;
                fmt_pkt_idx         <= fmt_pkt_idx_next;
                fmt_pkts_remaining  <= fmt_pkts_remaining_next;
                fmt_pkt_lens        <= fmt_pkt_lens_next;
                fmt_pkt_len_current <= fmt_pkt_len_current_next;
            end if;
        end if;
    end process;

    fmt_next_state_p : process (all)
    begin
        -- Default value
        fmt_state_next <= fmt_state;

        case fmt_state is
            when FMT_META =>
                if (out_fifo_rd = '1') then
                    fmt_state_next <= FMT_PAYLOAD;
                end if;

            when FMT_PAYLOAD =>
                if (out_fifo_rd = '1'                   and
                    fmt_remaining <= (DDR_DATA_WIDTH/8) and
                    fmt_pkts_remaining - 1 = 0) then
                    fmt_state_next <= FMT_META;
                end if;
        end case;
    end process;

    fmt_output_logic_p : process (all)
    begin
        -- Default values
        fmt_remaining_next       <= fmt_remaining;
        fmt_pkt_idx_next         <= fmt_pkt_idx;
        fmt_pkts_remaining_next  <= fmt_pkts_remaining;
        fmt_pkt_lens_next        <= fmt_pkt_lens;
        fmt_pkt_len_current_next <= fmt_pkt_len_current;

        TX_AXI_VALID <= '0';
        TX_AXI_LAST  <= '0';
        TX_AXI_KEEP  <= (others => '0');

        out_fifo_rd <= '0';

        case fmt_state is
            when FMT_META =>
                if (not out_fifo_empty) then
                    fmt_pkts_remaining_next  <= get_pkts_remaining(out_fifo_do);
                    fmt_pkt_lens_next        <= get_pkt_lens(out_fifo_do);
                    fmt_pkt_idx_next         <= (others => '0');
                    fmt_remaining_next       <= get_pkt_len(
                                                    get_pkt_lens(out_fifo_do),
                                                    (others => '0')
                                                );

                    -- Save packet length for output
                    fmt_pkt_len_current_next <= get_pkt_len(
                                                    get_pkt_lens(out_fifo_do),
                                                    (others => '0')
                                                );

                    out_fifo_rd <= '1';      -- pop metaword
                end if;

            when FMT_PAYLOAD =>
                if (out_fifo_empty = '0' and fmt_pkts_remaining > 0) then
                    TX_AXI_VALID <= '1';

                    -- Payload AXI formatting
                    if (fmt_remaining > (DDR_DATA_WIDTH/8)) then
                        TX_AXI_LAST <= '0';
                        TX_AXI_KEEP <= (others => '1');
                    else
                        TX_AXI_LAST <= '1';
                        TX_AXI_KEEP <= ones_mask(fmt_remaining);
                    end if;

                    -- Internal state updates only after AXI handshake
                    if (TX_AXI_READY = '1') then
                        out_fifo_rd <= '1'; -- Pop from fifo

                        if (fmt_remaining > (DDR_DATA_WIDTH/8)) then
                            -- Packet has not been fully read
                            fmt_remaining_next <= fmt_remaining - (DDR_DATA_WIDTH/8);
                        else
                            -- Full packet was read, move on to the next one
                            fmt_pkts_remaining_next <= fmt_pkts_remaining - 1;
                            fmt_pkt_idx_next        <= fmt_pkt_idx + 1;

                            if (fmt_pkts_remaining > 1) then
                                fmt_remaining_next       <= get_pkt_len(fmt_pkt_lens, fmt_pkt_idx + 1);
                                fmt_pkt_len_current_next <= get_pkt_len(fmt_pkt_lens, fmt_pkt_idx + 1);
                            end if;
                        end if;
                    end if;
                end if;
        end case;
    end process;

    TX_AXI_DATA <= out_fifo_do;
    TX_PKT_LEN  <= std_logic_vector(fmt_pkt_len_current);

end architecture;
