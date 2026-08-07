-- SPDX-License-Identifier: BSD-3-Clause
-- Copyright (C) 2024 CESNET z. s. p. o
-- Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- A hash-based key/value lookup table for the MVB bus. For every valid RX
-- item, the MVB_KEY_WIDTH-bit key is hashed by two independent hash
-- functions (a Toeplitz hash and a simple XOR hash, both keyed by the same
-- SW-configurable HASH_KEY), each indexing its own table implemented in a
-- separate ``SDP_MEMX`` memory (per MVB item, so 2*MVB_ITEMS
-- memories in total). Three clock cycles later, TX_MVB_DATA/TX_MVB_MATCH
-- report whether either table held a matching entry for that key (the
-- stored key is compared against the original lookup key to reject hash
-- collisions) and, if so, its stored data. TX_MVB_VLD simply follows
-- RX_MVB_VLD (delayed); it does **not** indicate a match - always check
-- TX_MVB_MATCH for that. When neither table matches, TX_MVB_DATA is
-- undefined (defaults to the XOR table's read data regardless of validity).
--
-- Table entries are written through the MI bus (see the WARNING below);
-- MVB lookups are used only for reading. Every MI_WR/MI_RD access, and the
-- whole "clear tables" sweep, stalls RX_MVB_DST_RDY for its duration - do
-- not expect full MVB throughput while configuring the table over MI.
--
-- .. WARNING::
--    TABLE_CAPACITY should be a power of two: HASH_WIDTH = log2(TABLE_CAPACITY)
--    is used directly as the address width of the hash functions and of the
--    underlying memories, without any additional range check.
--
-- .. WARNING::
--    There is no hash-collision detection on writes. A table address holds
--    exactly one entry, a write to 0x0C unconditionally overwrites whatever
--    is already stored there, and MI_RD never returns the actual table
--    content (only the configuration constants below) - so software has no
--    way to check what currently occupies an address before overwriting it.
--    The two independent tables (Toeplitz/XOR) exist to give software an
--    alternate slot for a colliding key, but choosing between them and
--    tracking which keys occupy which slots is entirely software's
--    responsibility; the hardware provides no support for it. This only
--    affects writes - a lookup for a key that collides with a different
--    key's stored entry is still handled safely (the stored-key comparison
--    makes it report TX_MVB_MATCH = '0', never wrong data).
--
-- MI register map
-- ----------------
--
-- Only the low 8 bits of MI_ADDR are decoded. All registers are MI_WIDTH
-- (commonly 32) bits wide.
--
-- +---------+------------------------------------------------------------+------------------------------+
-- | Address | Write (MI_WR)                                              | Read (MI_RD)                 |
-- +=========+============================================================+==============================+
-- | 0x00    | Command register, see below. Takes effect immediately (1   | Constant MVB_ITEMS.          |
-- |         | CLK).                                                      |                              |
-- +---------+------------------------------------------------------------+------------------------------+
-- | 0x04    | Table write address register (bits HASH_WIDTH-1 downto 0   | Constant MVB_KEY_WIDTH.      |
-- |         | of MI_DWR).                                                |                              |
-- +---------+------------------------------------------------------------+------------------------------+
-- | 0x08    | Shifts MI_DWR into the entry-data shift register, see the  | Constant DATA_OUT_WIDTH.     |
-- |         | NOTE below.                                                |                              |
-- +---------+------------------------------------------------------------+------------------------------+
-- | 0x0C    | Commits the entry-data shift register to the table         | Constant HASH_WIDTH (=       |
-- |         | selected by the command register, at the address set at    | log2(TABLE_CAPACITY)).       |
-- |         | 0x04. MI_DWR is ignored; only the write access itself (to  |                              |
-- |         | this address) matters.                                     |                              |
-- +---------+------------------------------------------------------------+------------------------------+
-- | 0x10    | Shifts MI_DWR into the hash-key register (shared by both   | Constant HASH_KEY_WIDTH.     |
-- |         | hash functions).                                           |                              |
-- +---------+------------------------------------------------------------+------------------------------+
-- | 0x14    | (no effect)                                                | Constant TABLE_CAPACITY.     |
-- +---------+------------------------------------------------------------+------------------------------+
--
-- .. NOTE::
--    An entry only actually changes in the table at the 0x0C commit; the
--    0x04/0x08 writes before it only prepare the new value and don't affect
--    the table yet. So an MVB lookup can never see a half-written entry -
--    only the complete old one or the complete new one.
--
--    MVB lookups are blocked for the one cycle of every individual MI
--    access (0x04, 0x08, or 0x0C), same as for the table-clearing sweep -
--    not just during the sweep. Between separate MI accesses, though, any
--    gap (a cycle with no MI_WR/MI_RD) lets lookups proceed as normal, so
--    they can still interleave with an in-progress multi-step entry update.
--    That's fine for the table content itself (as explained above), but if
--    your application additionally needs no lookups to happen at all for
--    the whole duration of an entry update, you need to arrange that
--    yourself; this component only blocks lookups access by access, not for
--    the whole sequence.
--
-- Command register (bits of the value written to address 0x00):
--
-- * bit 0 - select the Toeplitz table for the next 0x0C commit (0 = Toeplitz, 1 = XOR).
-- * bit 1 - start clearing (zeroing) both tables; self-clears when the sweep
--   finishes. While set, MI_ARDY stays deasserted for approximately
--   TABLE_CAPACITY clock cycles (a couple of cycles more in practice) and no
--   new MI request is accepted.
--
-- .. NOTE::
--    A stored entry is ``MVB_KEY_WIDTH + DATA_OUT_WIDTH + 1`` bits wide
--    (LSB to MSB: 1 valid bit, then DATA_OUT_WIDTH data bits, then the
--    MVB_KEY_WIDTH key), and is loaded into the entry-data shift register
--    with one or more writes to 0x08 (``ceil(entry_width / MI_WIDTH)``
--    writes, MI_WIDTH bits each). Each write shifts the new MI_DWR word in
--    at the *top*, so the **first** 0x08 write must carry the
--    **least-significant** MI_WIDTH-bit chunk of the entry (bits 0 and up,
--    i.e. the valid bit and low data bits) and the **last** write the
--    most-significant chunk (the key). The same shift-in convention (first
--    write = low bits) applies to the multi-word hash-key register at 0x10;
--    there the chunk boundaries only line up cleanly when HASH_KEY_WIDTH is
--    itself a multiple of MI_WIDTH (unlike the entry-data register, which is
--    rounded up to a whole number of MI_WIDTH chunks internally).
--
entity MVB_HASH_TABLE_SIMPLE is
    generic (
        -- Number of entries in each of the two hash tables.
        -- Should be a power of two, see the WARNING above.
        TABLE_CAPACITY    : natural := 256;
        -- Number of MVB items transferred in one word.
        -- Determines the number of instantiated SDP_MEMX memories (2*MVB_ITEMS).
        MVB_ITEMS         : natural := 4;
        -- Width of the MVB lookup key, in bits.
        MVB_KEY_WIDTH     : natural := 8;
        -- Width of the data value stored per table entry, in bits.
        DATA_OUT_WIDTH    : natural := 8;
        -- Width of the MI bus, in bits (typically 32, i.e. MI32).
        MI_WIDTH          : natural := 32;
        -- Width of the shared hash-key register (see the MI register map above), in bits.
        HASH_KEY_WIDTH    : natural := 32;
        -- Target FPGA device, passed through to the underlying SDP_MEMX memories.
        -- "7SERIES", "ULTRASCALE", "VERSAL", "ARRIA10", "STRATIX10", "AGILEX"
        DEVICE            : string  := "STRATIX10"
    );
    port (
        CLK               : in  std_logic;
        RST               : in  std_logic;

        -- ===========================================================================
        -- PORTS OF INPUT MVB BUS
        -- ===========================================================================
        RX_MVB_KEY        : in  std_logic_vector(MVB_ITEMS*MVB_KEY_WIDTH-1 downto 0);
        RX_MVB_VLD        : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY    : in  std_logic;
        -- Deasserted (regardless of TX_MVB_DST_RDY) while any MI access or
        -- table-clear sweep is in progress, see above.
        RX_MVB_DST_RDY    : out std_logic;

        -- ===========================================================================
        -- PORTS OF OUTPUT MVB BUS
        -- ===========================================================================
        -- Valid only where TX_MVB_MATCH = '1'.
        TX_MVB_DATA       : out std_logic_vector(MVB_ITEMS*DATA_OUT_WIDTH-1 downto 0);
        -- Set when a valid entry with a matching key was found in either table.
        TX_MVB_MATCH      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY    : out std_logic;
        TX_MVB_DST_RDY    : in  std_logic;

        -- ===========================================================================
        -- PORTS OF MI BUS
        --
        -- Used both to configure the hash key and write table entries, and
        -- to read back the component's configuration constants. See the MI
        -- register map above.
        -- ===========================================================================
        MI_ADDR           : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR            : in  std_logic_vector(MI_WIDTH-1 downto 0);
        -- Not used (present for MI bus interface compatibility only).
        MI_BE             : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_WR             : in  std_logic;
        MI_RD             : in  std_logic;
        MI_ARDY           : out std_logic;
        MI_DRD            : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DRDY           : out std_logic
    );
end entity;

architecture FULL of MVB_HASH_TABLE_SIMPLE is

    -- ===========================================================================
    -- DECLARATION OF CONTROL SIGNALS
    -- ===========================================================================
    constant TABLE_ITEM_WIDTH    : natural := MVB_KEY_WIDTH+DATA_OUT_WIDTH+1;
    constant DATA_WR_REG_WIDTH   : natural := div_roundup(TABLE_ITEM_WIDTH,MI_WIDTH)*MI_WIDTH;
    constant HASH_WIDTH          : natural := log2(TABLE_CAPACITY);
    signal   mvb_key_local       : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal   mi_addr_local       : unsigned(8-1 downto 0);
    signal   t_hash_out          : slv_array_t(MVB_ITEMS-1 downto 0)(HASH_WIDTH-1 downto 0);
    signal   t_mi_wr_en          : std_logic;
    signal   t_rd_data           : slv_array_t(MVB_ITEMS-1 downto 0)(TABLE_ITEM_WIDTH-1 downto 0);
    signal   t_wr_addr           : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal   t_wr_data           : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal   t_wr_en             : std_logic;
    signal   x_hash_out          : slv_array_t(MVB_ITEMS-1 downto 0)(HASH_WIDTH-1 downto 0);
    signal   x_mi_wr_en          : std_logic;
    signal   x_rd_data           : slv_array_t(MVB_ITEMS-1 downto 0)(TABLE_ITEM_WIDTH-1 downto 0);
    signal   x_wr_addr           : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal   x_wr_data           : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal   x_wr_en             : std_logic;
    signal   clear_wr_en         : std_logic;
    signal   clear_wr_en_vld     : std_logic;
    signal   clear_wr_addr       : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal   clear_wr_data       : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal   cap_cnt             : unsigned(HASH_WIDTH-1 downto 0);
    signal   ardy_en             : std_logic;
    signal   mi_wr_addr          : std_logic_vector(HASH_WIDTH-1 downto 0);
    signal   mi_wr_data          : std_logic_vector(TABLE_ITEM_WIDTH-1 downto 0);
    signal   cmd_reg             : std_logic_vector(2-1 downto 0);
    signal   mi_wr_data_reg      : std_logic_vector(DATA_WR_REG_WIDTH-1 downto 0);
    signal   table_choice        : std_logic;
    signal   hash_key            : std_logic_vector(HASH_KEY_WIDTH-1 downto 0);
    signal   src_rdy_reg         : std_logic_vector(3-1 downto 0);
    signal   mvb_vld_reg         : slv_array_t(MVB_ITEMS-1 downto 0)(3-1 downto 0);
    signal   prev_mvb_key_reg    : slv_array_t(MVB_ITEMS-1 downto 0)(2*MVB_KEY_WIDTH-1 downto 0);
    signal   prev_mvb_key        : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal   mvb_key_t           : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal   mvb_key_x           : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_KEY_WIDTH-1 downto 0);
    signal   mvb_data_t          : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal   mvb_data_x          : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal   prev_mvb_key_t_cmp  : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal   prev_mvb_key_x_cmp  : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal   match_t             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal   match_x             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal   out_data_sig        : slv_array_t(MVB_ITEMS-1 downto 0)(DATA_OUT_WIDTH-1 downto 0);
    signal   out_match_sig       : std_logic_vector(MVB_ITEMS-1 downto 0);

    -- ===========================================================================
    -- DEFINITION OF HASH FUNCTIONS
    -- ===========================================================================
    function f_toeplitz_hash (din : std_logic_vector; key : std_logic_vector) return std_logic_vector is
        variable v_hash      : std_logic_vector(HASH_WIDTH-1 downto 0);
        variable v_key_slice : std_logic_vector(HASH_WIDTH-1 downto 0);
        variable v_key_hash  : std_logic_vector(HASH_WIDTH-1 downto 0);
    begin
        v_hash := (others => '0');

        -- report "THASH: din=" & to_hstring(din) & "h";
        -- report "THASH: key=" & to_hstring(key) & "h";
        for i in din'length-1 downto 0 loop
            v_key_slice := key((key'length-(din'length-1-i)-1) downto (key'length-HASH_WIDTH-(din'length-1-i)));
            v_key_hash  := (others => '0');
            if (din(i) = '1') then
                v_key_hash := v_key_slice;
            end if;
            v_hash := v_hash xor v_key_hash;
        end loop;
        -- report "THASH: hash=" & to_hstring(v_hash) & "h";

        return v_hash;
    end function;

    function f_simple_xor_hash (din : std_logic_vector; key : std_logic_vector) return std_logic_vector is
        variable v_hash : std_logic_vector(HASH_WIDTH-1 downto 0);
    begin
        v_hash := din(HASH_WIDTH-1 downto 0) xor key(HASH_WIDTH-1 downto 0);

        return v_hash;
    end function;

begin

    mvb_key_local_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_key_local(g) <= RX_MVB_KEY((g+1)*MVB_KEY_WIDTH-1 downto g*MVB_KEY_WIDTH);
    end generate;

    mi_addr_local <= unsigned(MI_ADDR(mi_addr_local'length-1 downto 0));

    -- ===========================================================================
    -- SETTING HASH KEY AND RUNNING HASH FUNCTIONS
    -- ===========================================================================
    hash_functions_g: for g in 0 to MVB_ITEMS-1 generate
        t_hash_out(g) <= f_toeplitz_hash(mvb_key_local(g), hash_key)(HASH_WIDTH-1 downto 0);
        x_hash_out(g) <= f_simple_xor_hash(mvb_key_local(g), hash_key)(HASH_WIDTH-1 downto 0);
    end generate;

    -- ===========================================================================
    -- SDP_MEMX MEMORY MODULES
    -- ===========================================================================
    toeplitz_hash_table_g: for g in 0 to MVB_ITEMS-1 generate
        toeplitz_hash_table_i: entity work.SDP_MEMX
        generic map (
            DATA_WIDTH   => MVB_KEY_WIDTH + DATA_OUT_WIDTH + 1,
            ITEMS        => TABLE_CAPACITY,
            DEVICE       => DEVICE,
            RAM_TYPE     => "AUTO",
            OUTPUT_REG   => True
        )
        port map (
            CLK          => CLK,
            RESET        => RST,
            RD_ADDR      => t_hash_out(g),
            RD_DATA      => t_rd_data(g),
            RD_PIPE_EN   => TX_MVB_DST_RDY,
            WR_ADDR      => t_wr_addr,
            WR_DATA      => t_wr_data,
            WR_EN        => t_wr_en
        );
    end generate;

    simple_xor_hash_table_g: for g in 0 to MVB_ITEMS-1 generate
        simple_xor_hash_table_i: entity work.SDP_MEMX
        generic map (
            DATA_WIDTH   => MVB_KEY_WIDTH + DATA_OUT_WIDTH + 1,
            ITEMS        => TABLE_CAPACITY,
            DEVICE       => DEVICE,
            RAM_TYPE     => "AUTO",
            OUTPUT_REG   => True
        )
        port map (
            CLK          => CLK,
            RESET        => RST,
            RD_ADDR      => x_hash_out(g),
            RD_DATA      => x_rd_data(g),
            RD_PIPE_EN   => TX_MVB_DST_RDY,
            WR_ADDR      => x_wr_addr,
            WR_DATA      => x_wr_data,
            WR_EN        => x_wr_en
        );
    end generate;

    -- ===========================================================================
    -- MI COMMAND REGISTER
    -- ===========================================================================
    mi_cmd_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"00")) then
                cmd_reg <= MI_DWR(2-1 downto 0);
            end if;

            if (clear_wr_en_vld = '0') then
                cmd_reg(1)  <= '0';
            end if;

            if (RST = '1') then
                cmd_reg <= (others => '0');
            end if;
        end if;
    end process;

    table_choice <= cmd_reg(0);
    clear_wr_en  <= cmd_reg(1);

    -- ===========================================================================
    -- MI ADDRESS REGISTER
    -- ===========================================================================
    mi_addr_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"04")) then
                mi_wr_addr <= MI_DWR(mi_wr_addr'length-1 downto 0);
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- MI DATA REGISTER
    -- ===========================================================================
    mi_data_reg_p : process (CLK)
        variable be_dwr : std_logic_vector(MI_DWR'LENGTH-1 downto 0);
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"08")) then
                mi_wr_data_reg <= MI_DWR & mi_wr_data_reg(mi_wr_data_reg'high downto mi_wr_data_reg'low + MI_DWR'LENGTH);
            end if;

            if (RST = '1') then
                mi_wr_data_reg <= (others => '0');
            end if;
        end if;
    end process;

    mi_wr_data <= mi_wr_data_reg(mi_wr_data'length-1 downto 0);

    -- ===========================================================================
    -- MI WRITE ENABLE REGISTER
    -- ===========================================================================
    mi_write_en_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"0C")) then
                t_mi_wr_en <= not table_choice;
                x_mi_wr_en <= table_choice;
            else
                t_mi_wr_en <= '0';
                x_mi_wr_en <= '0';
            end if;

            if (RST = '1') then
                t_mi_wr_en <= '0';
                x_mi_wr_en <= '0';
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- HASH KEY CONFIGURATION REGISTER
    -- ===========================================================================
    hash_key_config_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if ((MI_WR = '1') and (mi_addr_local = X"10")) then
                hash_key <= MI_DWR & hash_key(hash_key'high downto hash_key'low + MI_DWR'LENGTH);
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- CLEAR TABLE
    -- ===========================================================================
    clear_table_p : process (CLK)
    begin
        if rising_edge(CLK) then
            clear_wr_en_vld <= '1';
            clear_wr_addr   <= std_logic_vector(cap_cnt);

            if (clear_wr_en = '1') then
                if (cap_cnt = TABLE_CAPACITY-1) then
                    clear_wr_en_vld <= '0';
                    ardy_en         <= '1';
                else
                    ardy_en         <= '0';
                end if;

            else
                ardy_en             <= '1';
            end if;

            if (RST = '1') then
                clear_wr_en_vld     <= '0';
                ardy_en             <= '1';
            end if;
        end if;
    end process;

    clear_wr_data <= (others => '0');

    clear_table_cntr_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (clear_wr_en = '1') then
                cap_cnt <= cap_cnt + 1;
            else
                cap_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- CONFIGURATION READOUT
    -- ===========================================================================
    capacity_readout_p : process (CLK)
    begin
        if rising_edge(CLK) then
            case mi_addr_local is
                when X"00"      => MI_DRD <= std_logic_vector(to_unsigned(MVB_ITEMS, MI_DRD'LENGTH));
                when X"04"      => MI_DRD <= std_logic_vector(to_unsigned(MVB_KEY_WIDTH, MI_DRD'LENGTH));
                when X"08"      => MI_DRD <= std_logic_vector(to_unsigned(DATA_OUT_WIDTH, MI_DRD'LENGTH));
                when X"0C"      => MI_DRD <= std_logic_vector(to_unsigned(HASH_WIDTH, MI_DRD'LENGTH));
                when X"10"      => MI_DRD <= std_logic_vector(to_unsigned(HASH_KEY_WIDTH, MI_DRD'LENGTH));
                when X"14"      => MI_DRD <= std_logic_vector(to_unsigned(TABLE_CAPACITY, MI_DRD'LENGTH));
                when others => NULL;
            end case;

            MI_DRDY <= MI_RD;

            if (RST = '1') then
                MI_DRDY <= '0';
            end if;
        end if;
    end process;

    -- ===========================================================================
    -- MVB KEY COMPARATOR
    -- ===========================================================================
    mvb_key_comparator_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_key_t(g) <= t_rd_data(g)(TABLE_ITEM_WIDTH-1 downto DATA_OUT_WIDTH+1);
        mvb_key_x(g) <= x_rd_data(g)(TABLE_ITEM_WIDTH-1 downto DATA_OUT_WIDTH+1);

        mvb_data_t(g) <= t_rd_data(g)(DATA_OUT_WIDTH downto 1);
        mvb_data_x(g) <= x_rd_data(g)(DATA_OUT_WIDTH downto 1);

        prev_mvb_key_t_cmp(g) <= '1' when (mvb_key_t(g) = prev_mvb_key(g)) else '0';
        prev_mvb_key_x_cmp(g) <= '1' when (mvb_key_x(g) = prev_mvb_key(g)) else '0';

        match_t(g) <= t_rd_data(g)(0) and prev_mvb_key_t_cmp(g);
        match_x(g) <= x_rd_data(g)(0) and prev_mvb_key_x_cmp(g);

        out_data_sig(g)  <= mvb_data_t(g) when (match_t(g) = '1') else mvb_data_x(g);
        out_match_sig(g) <= match_t(g) or match_x(g);

        mvb_key_comparator_p : process (CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    TX_MVB_DATA((g+1)*DATA_OUT_WIDTH-1 downto g*DATA_OUT_WIDTH) <= out_data_sig(g);
                    TX_MVB_MATCH(g)                                             <= out_match_sig(g);
                end if;
            end if;
        end process;
    end generate;

    -- ===========================================================================
    -- PREVIOUS MVB KEY SHIFT REGISTERS
    -- ===========================================================================
    prev_mvb_key_shift_reg_g: for g in 0 to MVB_ITEMS-1 generate
        prev_mvb_key_shift_reg_p : process (CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    prev_mvb_key_reg(g) <= prev_mvb_key_reg(g)(prev_mvb_key_reg(g)'high - MVB_KEY_WIDTH downto prev_mvb_key_reg(g)'low) & mvb_key_local(g);
                end if;
            end if;
        end process;

        prev_mvb_key(g) <= prev_mvb_key_reg(g)(prev_mvb_key_reg(g)'high downto prev_mvb_key_reg(g)'high - MVB_KEY_WIDTH + 1);
    end generate;

    -- ===========================================================================
    -- TX_MVB_SRC_RDY SHIFT REGISTERS
    -- ===========================================================================
    src_rdy_shift_reg_p : process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_MVB_DST_RDY = '1') then
                src_rdy_reg <= src_rdy_reg(src_rdy_reg'high - 1 downto src_rdy_reg'low) & RX_MVB_SRC_RDY;
            end if;

            if (RST = '1') then
                src_rdy_reg <= (others => '0');
            end if;
        end if;
    end process;

    TX_MVB_SRC_RDY <= src_rdy_reg(src_rdy_reg'high);

    -- ===========================================================================
    -- MVB VLD SIGNAL SHIFT REGISTERS
    -- ===========================================================================
    mvb_vld_shift_reg_g: for g in 0 to MVB_ITEMS-1 generate
        mvb_vld_shift_reg_p : process (CLK)
        begin
            if rising_edge(CLK) then
                if (TX_MVB_DST_RDY = '1') then
                    mvb_vld_reg(g) <= mvb_vld_reg(g)(mvb_vld_reg(g)'high - 1 downto mvb_vld_reg(g)'low) & RX_MVB_VLD(g);
                end if;

                if (RST = '1') then
                    mvb_vld_reg(g) <= (others => '0');
                end if;
            end if;
        end process;

        TX_MVB_VLD(g)  <= mvb_vld_reg(g)(mvb_vld_reg(g)'high);
    end generate;

    -- ===========================================================================
    -- OUTPUT SIGNALS
    -- ===========================================================================
    RX_MVB_DST_RDY       <= TX_MVB_DST_RDY when (MI_WR = '0' and MI_RD = '0' and clear_wr_en = '0') else '0';

    MI_ARDY              <= (MI_WR or MI_RD) and ardy_en;

    t_wr_en              <= t_mi_wr_en or clear_wr_en;
    t_wr_addr            <= clear_wr_addr when clear_wr_en = '1' else mi_wr_addr;
    t_wr_data            <= clear_wr_data when clear_wr_en = '1' else mi_wr_data;

    x_wr_en              <= x_mi_wr_en or clear_wr_en;
    x_wr_addr            <= clear_wr_addr when clear_wr_en = '1' else mi_wr_addr;
    x_wr_data            <= clear_wr_data when clear_wr_en = '1' else mi_wr_data;

end architecture;
