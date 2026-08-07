-- mvb_lut.vhd: MVB Lookup table with SW configuration (TOP implementation)
-- Copyright (C) 2022 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- MVB Lookup Table: for every valid MVB item on the RX side, looks up the
-- table entry addressed by RX_MVB_LUT_ADDR and presents it on the
-- corresponding TX_MVB_LUT_DATA item, together with the (registered)
-- RX_MVB_LUT_ADDR and RX_MVB_METADATA of that item. This is the top-level
-- (recommended) entity: it picks one of the three available implementations
-- (a single register, ``MVB_LOOKUP_TABLE_LUTRAM``, or
-- ``MVB_LOOKUP_TABLE_BRAM``) based on LUT_ARCH/LUT_DEPTH. RX-to-TX latency
-- depends on which of these is selected and on OUTPUT_REG, see the
-- OUTPUT_REG generic below for the exact cycle counts.
--
-- The table content is configured through a synchronous SW_* register-file
-- style port (address + byte-enabled data, not the CESNET MI bus) - see the
-- port descriptions below. This component does **not** reset or initialize
-- the table content on RESET; all LUT_DEPTH entries must be written through
-- the SW_* interface before the first RX lookup that relies on them,
-- otherwise reads of not-yet-written entries return undefined data.
--
-- .. NOTE::
--    SW_WRITE never stalls or backpressures RX_MVB lookups - RX_MVB_DST_RDY
--    only follows TX_MVB_DST_RDY, regardless of SW_* activity. Unlike some
--    sibling components, there is also no atomicity guarantee here, not even
--    for a single entry: each SW_WRITE goes straight into the table as soon
--    as it happens, with no staging step that only commits a complete entry
--    at once. So if LUT_WIDTH > SW_WIDTH, an entry needs several SW_WRITEs
--    (one per slice, see above) to fully update, and an RX_MVB lookup
--    running in between can see that *one* entry half-written - part old
--    slices, part new.
--
--    The same applies, entry by entry, when updating several entries in a
--    row. If your application needs lookups to only ever see a fully
--    consistent entry (or a consistent snapshot across several entries), you
--    need to arrange that yourself, e.g. by pausing RX_MVB lookups for the
--    duration of an update; this component does not do it for you.
--
-- .. WARNING::
--    LUT_WIDTH must be an integer multiple of SW_WIDTH. Any other ratio is
--    not correctly supported: depending on LUT_DEPTH/LUT_ARCH it causes the
--    topmost bits of an entry to be silently unreachable through SW_DOUT
--    (single register and ``MVB_LOOKUP_TABLE_BRAM``), aliased writes
--    (single register), or an elaboration-time width mismatch
--    (``MVB_LOOKUP_TABLE_BRAM``). ``MVB_LOOKUP_TABLE_LUTRAM`` handles the
--    entry width itself correctly, but the shared SW_SLICE port is always
--    sized for the exact-multiple case, so higher slices can still be
--    unreachable there too.
--
entity MVB_LOOKUP_TABLE is
    generic (
        -- Number of MVB items transferred in one word.
        MVB_ITEMS  : natural := 4;
        -- Number of entries in the lookup table.
        -- Any positive value; LUT_DEPTH = 1 is implemented directly as a
        -- single shared register regardless of LUT_ARCH.
        LUT_DEPTH  : natural := 128;
        -- Width of one lookup table entry in bits.
        -- Should be a multiple of SW_WIDTH, see the WARNING above.
        LUT_WIDTH  : natural := 32;
        -- Select the memory implementation used when LUT_DEPTH > 1:
        --
        -- * "LUT"  - ``MVB_LOOKUP_TABLE_LUTRAM``, effective for a shallow table (approx. LUT_DEPTH <= 64).
        -- * "BRAM" - ``MVB_LOOKUP_TABLE_BRAM``, effective for a deep table (approx. LUT_DEPTH > 64); consumes MVB_ITEMS+1 block RAMs.
        -- * "AUTO" - chosen automatically from LUT_DEPTH using the same approx. 64-entry threshold as above.
        LUT_ARCH   : string  := "AUTO";
        -- Data width of the SW_* configuration port in bits.
        -- Must be a multiple of 8: SW_BE has one bit per byte of SW_DIN
        -- (SW_WIDTH/8, integer division), so a non-multiple silently loses
        -- byte-enable coverage over the trailing, incomplete byte.
        SW_WIDTH   : natural := 32;
        -- Width of the RX_MVB_METADATA/TX_MVB_METADATA side-channel in bits.
        -- Any non-negative value; the metadata is only delayed together with
        -- the MVB transaction, it does not influence the lookup itself.
        META_WIDTH : natural := 1;
        -- Adds an output register stage on the TX_MVB_* path (and, for the
        -- BRAM implementation, also on the internal RAM output). Improves
        -- timing at the cost of extra registers and one additional CLK
        -- cycle of RX-to-TX latency:
        --
        -- * Single register (LUT_DEPTH = 1) or LUT_ARCH = "LUT": 0 CLK cycles
        --   when false, 1 CLK cycle when true.
        -- * LUT_ARCH = "BRAM": 1 CLK cycle when false, 2 CLK cycles when true.
        OUTPUT_REG : boolean := True;
        -- Target FPGA device, passed through to the underlying memory
        -- implementation.
        DEVICE     : string  := "AGILEX"
    );
    port (
        CLK             : in  std_logic;
        RESET           : in  std_logic;

        -- =====================================================================
        -- RX MVB INTERFACE
        --
        -- Lookup request: RX_MVB_LUT_ADDR addresses the entry to look up.
        -- =====================================================================

        RX_MVB_LUT_ADDR : in  slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
        RX_MVB_METADATA : in  slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY  : in  std_logic;
        RX_MVB_DST_RDY  : out std_logic;

        -- =====================================================================
        -- TX MVB INTERFACE
        --
        -- Lookup result, RX-to-TX latency cycles later (see OUTPUT_REG above).
        -- =====================================================================

        -- Lookup table entry addressed by the corresponding (registered) TX_MVB_LUT_ADDR.
        TX_MVB_LUT_DATA : out slv_array_t(MVB_ITEMS-1 downto 0)(LUT_WIDTH-1 downto 0);
        TX_MVB_LUT_ADDR : out slv_array_t(MVB_ITEMS-1 downto 0)(max(log2(LUT_DEPTH),1)-1 downto 0);
        TX_MVB_METADATA : out slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
        TX_MVB_VLD      : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY  : out std_logic;
        TX_MVB_DST_RDY  : in  std_logic;

        -- =====================================================================
        -- SW CONFIGURATION INTERFACE
        --
        -- Synchronous register-file style port used to read/write the lookup
        -- table content. Not the CESNET MI bus; intended to be driven
        -- through an external MI (or other software-accessible bus) adapter.
        -- One access addresses a single LUT entry (SW_ADDR). If LUT_WIDTH is
        -- wider than SW_WIDTH, each access only reaches one SW_WIDTH-wide
        -- slice of that entry, chosen by SW_SLICE. Writing a whole entry
        -- therefore means repeating SW_WRITE at the same SW_ADDR once per
        -- slice, SW_SLICE = 0 to LUT_WIDTH/SW_WIDTH-1.
        -- =====================================================================

        -- Address of the accessed lookup table entry.
        SW_ADDR         : in  std_logic_vector(max(log2(LUT_DEPTH),1)-1 downto 0);
        -- Selects which SW_WIDTH-wide slice of the addressed entry is
        -- accessed, when LUT_WIDTH > SW_WIDTH. Unused (any value valid) when
        -- LUT_WIDTH = SW_WIDTH (the only other case the WARNING above allows).
        SW_SLICE        : in  std_logic_vector(max(log2(LUT_WIDTH/SW_WIDTH),1)-1 downto 0);
        -- Data to write; valid when SW_WRITE = '1'.
        SW_DIN          : in  std_logic_vector(SW_WIDTH-1 downto 0);
        -- Byte-enable for SW_DIN; only enabled bytes are written.
        SW_BE           : in  std_logic_vector(SW_WIDTH/8-1 downto 0);
        -- Write request for the (SW_ADDR, SW_SLICE) location, takes effect immediately (1 CLK).
        SW_WRITE        : in  std_logic;
        -- Read request for the (SW_ADDR, SW_SLICE) location; the result appears on SW_DOUT one CLK later.
        SW_READ         : in  std_logic;
        -- Read data, valid when SW_DOUT_VLD = '1' (registered, one CLK after SW_READ).
        SW_DOUT         : out std_logic_vector(SW_WIDTH-1 downto 0);
        SW_DOUT_VLD     : out std_logic
    );
end entity;

architecture FULL of MVB_LOOKUP_TABLE is

    constant LUT_BYTES_W      : natural := LUT_WIDTH/8;
    constant SW_WORDS_PER_LUT : natural := LUT_WIDTH/SW_WIDTH;
    constant SW_BYTES_W       : natural := SW_WIDTH/8;

    signal lram_sel           : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr            : std_logic_vector(LUT_BYTES_W-1 downto 0);
    signal lram_wr_data       : slv_array_t(LUT_BYTES_W-1 downto 0)(8-1 downto 0);

    signal lut_reg_arr        : slv_array_t(LUT_BYTES_W-1 downto 0)(8-1 downto 0);
    signal lut_reg            : std_logic_vector(LUT_WIDTH-1 downto 0);

    signal lut_reg_sw_nsw     : std_logic_vector(SW_WORDS_PER_LUT*SW_WIDTH-1 downto 0);
    signal lut_reg_sw_nsw_arr : slv_array_t(SW_WORDS_PER_LUT-1 downto 0)(SW_WIDTH-1 downto 0);
    signal lut_reg_sw         : std_logic_vector(SW_WIDTH-1 downto 0);

begin

    single_reg_g: if (LUT_DEPTH = 1) generate
        RX_MVB_DST_RDY <= TX_MVB_DST_RDY;

        lreg_g: for i in 0 to LUT_BYTES_W-1 generate
            lram_sel_g : if SW_WORDS_PER_LUT > 1 generate
                lram_sel(i) <= '1' when (unsigned(SW_SLICE) = (i/SW_BYTES_W)) else '0';
            else generate
                lram_sel(i) <= '1';
            end generate;
            lram_wr(i)      <= lram_sel(i) and SW_BE(i mod SW_BYTES_W) and SW_WRITE;
            lram_wr_data(i) <= SW_DIN(((i mod SW_BYTES_W)+1)*8-1 downto (i mod SW_BYTES_W)*8);

            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (lram_wr(i) = '1') then
                        lut_reg_arr(i) <= lram_wr_data(i);
                    end if;
                end if;
            end process;
        end generate;

        lut_reg <= slv_array_ser(lut_reg_arr);

        lut_reg_sw_nsw     <= std_logic_vector(resize(unsigned(lut_reg),(SW_WORDS_PER_LUT*SW_WIDTH)));
        lut_reg_sw_nsw_arr <= slv_array_deser(lut_reg_sw_nsw,SW_WORDS_PER_LUT);

        process (all)
        begin
            if (SW_WORDS_PER_LUT > 1) then
                lut_reg_sw <= (others => '0');
                for i in 0 to SW_WORDS_PER_LUT-1 loop
                    if (unsigned(SW_SLICE) = i) then
                        lut_reg_sw <= lut_reg_sw_nsw_arr(i);
                    end if;
                end loop;
            else
                lut_reg_sw <= lut_reg_sw_nsw_arr(0);
            end if;
        end process;

        process (CLK)
        begin
            if (rising_edge(CLK)) then
                SW_DOUT     <= lut_reg_sw;
                SW_DOUT_VLD <= SW_READ;
                if (RESET = '1') then
                    SW_DOUT_VLD <= '0';
                end if;
            end if;
        end process;

        out_reg_g: if OUTPUT_REG generate
            process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (TX_MVB_DST_RDY = '1') then
                        TX_MVB_METADATA <= RX_MVB_METADATA;
                        TX_MVB_LUT_ADDR <= RX_MVB_LUT_ADDR;
                        TX_MVB_LUT_DATA <= (others => lut_reg);
                        TX_MVB_VLD      <= RX_MVB_VLD;
                        TX_MVB_SRC_RDY  <= RX_MVB_SRC_RDY;
                    end if;
                    if (RESET = '1') then
                        TX_MVB_SRC_RDY <= '0';
                    end if;
                end if;
            end process;
        else generate
            TX_MVB_METADATA <= RX_MVB_METADATA;
            TX_MVB_LUT_ADDR <= RX_MVB_LUT_ADDR;
            TX_MVB_LUT_DATA <= (others => lut_reg);
            TX_MVB_VLD      <= RX_MVB_VLD;
            TX_MVB_SRC_RDY  <= RX_MVB_SRC_RDY;
        end generate;
    end generate;

    lutram_g: if ((LUT_DEPTH > 1 and LUT_DEPTH <= 64 and LUT_ARCH = "AUTO") or (LUT_DEPTH > 1 and LUT_ARCH = "LUT")) generate
        lutram_i : entity work.MVB_LOOKUP_TABLE_LUTRAM
        generic map (
            MVB_ITEMS  => MVB_ITEMS,
            LUT_DEPTH  => LUT_DEPTH,
            LUT_WIDTH  => LUT_WIDTH,
            SW_WIDTH   => SW_WIDTH,
            META_WIDTH => META_WIDTH,
            OUTPUT_REG => OUTPUT_REG,
            DEVICE     => DEVICE
        )
        port map (
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_LUT_ADDR => RX_MVB_LUT_ADDR,
            RX_MVB_METADATA => RX_MVB_METADATA,
            RX_MVB_VLD      => RX_MVB_VLD,
            RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

            TX_MVB_LUT_DATA => TX_MVB_LUT_DATA,
            TX_MVB_LUT_ADDR => TX_MVB_LUT_ADDR,
            TX_MVB_METADATA => TX_MVB_METADATA,
            TX_MVB_VLD      => TX_MVB_VLD,
            TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

            SW_ADDR         => SW_ADDR,
            SW_SLICE        => SW_SLICE,
            SW_DIN          => SW_DIN,
            SW_BE           => SW_BE,
            SW_WRITE        => SW_WRITE,
            SW_READ         => SW_READ,
            SW_DOUT         => SW_DOUT,
            SW_DOUT_VLD     => SW_DOUT_VLD
        );
    end generate;

    bram_g: if ((LUT_DEPTH > 64 and LUT_ARCH = "AUTO") or (LUT_DEPTH > 1 and LUT_ARCH = "BRAM")) generate
        bram_i : entity work.MVB_LOOKUP_TABLE_BRAM
        generic map (
            MVB_ITEMS  => MVB_ITEMS,
            LUT_DEPTH  => LUT_DEPTH,
            LUT_WIDTH  => LUT_WIDTH,
            SW_WIDTH   => SW_WIDTH,
            META_WIDTH => META_WIDTH,
            OUTPUT_REG => OUTPUT_REG,
            DEVICE     => DEVICE
        )
        port map (
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_LUT_ADDR => RX_MVB_LUT_ADDR,
            RX_MVB_METADATA => RX_MVB_METADATA,
            RX_MVB_VLD      => RX_MVB_VLD,
            RX_MVB_SRC_RDY  => RX_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => RX_MVB_DST_RDY,

            TX_MVB_LUT_DATA => TX_MVB_LUT_DATA,
            TX_MVB_LUT_ADDR => TX_MVB_LUT_ADDR,
            TX_MVB_METADATA => TX_MVB_METADATA,
            TX_MVB_VLD      => TX_MVB_VLD,
            TX_MVB_SRC_RDY  => TX_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => TX_MVB_DST_RDY,

            SW_ADDR         => SW_ADDR,
            SW_SLICE        => SW_SLICE,
            SW_DIN          => SW_DIN,
            SW_BE           => SW_BE,
            SW_WRITE        => SW_WRITE,
            SW_READ         => SW_READ,
            SW_DOUT         => SW_DOUT,
            SW_DOUT_VLD     => SW_DOUT_VLD
        );
    end generate;

end architecture;
