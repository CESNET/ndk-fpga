-- dma_bus_pack.vhd: DMA Bus Package
-- Copyright (C) 2017 CESNET
-- Author: Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        DMA BUS package
-- ----------------------------------------------------------------------------

-- Items description
--
-- ========= ==================================================================
-- LENGTH    Lenght of data in current request/completion in DWORDs (4B); for read request it is a requested size
-- TYPE      Request type, currently only read and write requests are supported
-- FIRSTIB   First invalid bytes - specifies, how many bytes at first data word are invalid; used to generate First BE
-- LASTIB    Last invalid bytes - specifies, how many bytes at last data word are invalid; used to generate Last BE
-- TAG       Transaction ID unique in scope of current unit; it will be translated to an PCI tag together with UNITID
-- UNITID    Transaction ID unique for each unit (in scope of 1 endpoint) and is used for routing of completions
-- GLOBAL    Global 64b address to main memory space of request
-- VFID      Virtual function ID for specifying PCI function
-- PASID     Process Address Space ID for better granularity of virtualization
-- PASIDVLD  PASID value is valid and will be used to generate TLP PASID prefix
-- RELAXED   Relaxed ordering in the mean of PCIe standard; typically needs to be set in all read requests
-- ========= ==================================================================
package dma_bus_pack is

    constant DMA_REQUEST_LENGTH_W       : natural := 11;
    constant DMA_REQUEST_TYPE_W         : natural := 1;
    constant DMA_REQUEST_FIRSTIB_W      : natural := 2;
    constant DMA_REQUEST_LASTIB_W       : natural := 2;
    constant DMA_REQUEST_TAG_W          : natural := 8;
    constant DMA_REQUEST_UNITID_W       : natural := 8;
    constant DMA_REQUEST_GLOBAL_W       : natural := 64;
    constant DMA_REQUEST_VFID_W         : natural := 8;
    constant DMA_REQUEST_PASID_W        : natural := 0;
    constant DMA_REQUEST_PASIDVLD_W     : natural := 0;
    constant DMA_REQUEST_RELAXED_W      : natural := 1;

    constant DMA_COMPLETION_LENGTH_W    : natural := 11;
    constant DMA_COMPLETION_COMPLETED_W : natural := 1;
    constant DMA_COMPLETION_TAG_W       : natural := 8;
    constant DMA_COMPLETION_UNITID_W    : natural := 8;

    constant DMA_REQUEST_LENGTH_O       : natural := 0;
    constant DMA_REQUEST_TYPE_O         : natural := DMA_REQUEST_LENGTH_O           + DMA_REQUEST_LENGTH_W;
    constant DMA_REQUEST_FIRSTIB_O      : natural := DMA_REQUEST_TYPE_O             + DMA_REQUEST_TYPE_W;
    constant DMA_REQUEST_LASTIB_O       : natural := DMA_REQUEST_FIRSTIB_O          + DMA_REQUEST_FIRSTIB_W;
    constant DMA_REQUEST_TAG_O          : natural := DMA_REQUEST_LASTIB_O           + DMA_REQUEST_LASTIB_W;
    constant DMA_REQUEST_UNITID_O       : natural := DMA_REQUEST_TAG_O              + DMA_REQUEST_TAG_W;
    constant DMA_REQUEST_GLOBAL_O       : natural := DMA_REQUEST_UNITID_O           + DMA_REQUEST_UNITID_W;
    constant DMA_REQUEST_VFID_O         : natural := DMA_REQUEST_GLOBAL_O           + DMA_REQUEST_GLOBAL_W;
    constant DMA_REQUEST_PASID_O        : natural := DMA_REQUEST_VFID_O             + DMA_REQUEST_VFID_W;
    constant DMA_REQUEST_PASIDVLD_O     : natural := DMA_REQUEST_PASID_O            + DMA_REQUEST_PASID_W;
    constant DMA_REQUEST_RELAXED_O      : natural := DMA_REQUEST_PASIDVLD_O         + DMA_REQUEST_PASIDVLD_W;

    constant DMA_COMPLETION_LENGTH_O    : natural := 0;
    constant DMA_COMPLETION_COMPLETED_O : natural := DMA_COMPLETION_LENGTH_O        + DMA_COMPLETION_LENGTH_W;
    constant DMA_COMPLETION_TAG_O       : natural := DMA_COMPLETION_COMPLETED_O     + DMA_COMPLETION_COMPLETED_W;
    constant DMA_COMPLETION_UNITID_O    : natural := DMA_COMPLETION_TAG_O           + DMA_COMPLETION_TAG_W;

    subtype DMA_REQUEST_LENGTH          is natural range DMA_REQUEST_LENGTH_O       + DMA_REQUEST_LENGTH_W      -1 downto DMA_REQUEST_LENGTH_O;
    subtype DMA_REQUEST_TYPE            is natural range DMA_REQUEST_TYPE_O         + DMA_REQUEST_TYPE_W        -1 downto DMA_REQUEST_TYPE_O;
    subtype DMA_REQUEST_FIRSTIB         is natural range DMA_REQUEST_FIRSTIB_O      + DMA_REQUEST_FIRSTIB_W     -1 downto DMA_REQUEST_FIRSTIB_O;
    subtype DMA_REQUEST_LASTIB          is natural range DMA_REQUEST_LASTIB_O       + DMA_REQUEST_LASTIB_W      -1 downto DMA_REQUEST_LASTIB_O;
    subtype DMA_REQUEST_TAG             is natural range DMA_REQUEST_TAG_O          + DMA_REQUEST_TAG_W         -1 downto DMA_REQUEST_TAG_O;
    subtype DMA_REQUEST_UNITID          is natural range DMA_REQUEST_UNITID_O       + DMA_REQUEST_UNITID_W      -1 downto DMA_REQUEST_UNITID_O;
    subtype DMA_REQUEST_GLOBAL          is natural range DMA_REQUEST_GLOBAL_O       + DMA_REQUEST_GLOBAL_W      -1 downto DMA_REQUEST_GLOBAL_O;
    subtype DMA_REQUEST_VFID            is natural range DMA_REQUEST_VFID_O         + DMA_REQUEST_VFID_W        -1 downto DMA_REQUEST_VFID_O;
    subtype DMA_REQUEST_PASID           is natural range DMA_REQUEST_PASID_O        + DMA_REQUEST_PASID_W       -1 downto DMA_REQUEST_PASID_O;
    subtype DMA_REQUEST_PASIDVLD        is natural range DMA_REQUEST_PASIDVLD_O     + DMA_REQUEST_PASIDVLD_W    -1 downto DMA_REQUEST_PASIDVLD_O;
    subtype DMA_REQUEST_RELAXED         is natural range DMA_REQUEST_RELAXED_O      + DMA_REQUEST_RELAXED_W     -1 downto DMA_REQUEST_RELAXED_O;

    subtype DMA_COMPLETION_LENGTH       is natural range DMA_COMPLETION_LENGTH_O    + DMA_COMPLETION_LENGTH_W   -1 downto DMA_COMPLETION_LENGTH_O;
    subtype DMA_COMPLETION_COMPLETED    is natural range DMA_COMPLETION_COMPLETED_O + DMA_COMPLETION_COMPLETED_W-1 downto DMA_COMPLETION_COMPLETED_O;
    subtype DMA_COMPLETION_TAG          is natural range DMA_COMPLETION_TAG_O       + DMA_COMPLETION_TAG_W      -1 downto DMA_COMPLETION_TAG_O;
    subtype DMA_COMPLETION_UNITID       is natural range DMA_COMPLETION_UNITID_O    + DMA_COMPLETION_UNITID_W   -1 downto DMA_COMPLETION_UNITID_O;

    constant DMA_UPHDR_WIDTH            : natural := DMA_REQUEST_RELAXED_O          + DMA_REQUEST_RELAXED_W;
    constant DMA_DOWNHDR_WIDTH          : natural := DMA_COMPLETION_UNITID_O        + DMA_COMPLETION_UNITID_W;

    constant DMA_TYPE_WRITE             : std_logic_vector(0 downto 0) := "1";
    constant DMA_TYPE_READ              : std_logic_vector(0 downto 0) := "0";

    type dma_route_path_t is record
        routing_bit       : natural;    -- absolute bit position inside UNIT_ID
        siblings_count    : natural;    -- number of children of the *parent* junction
        child_index       : natural;    -- which child this path represents (0..siblings_count‑1)
    end record;

    type dma_route_junction_t is record
        routing_bit       : natural;    -- bit reserved for this junction (same as path.routing_bit)
        child_count       : natural;    -- number of children that stem from this junction
    end record;


    pure function dma_route_path_default return dma_route_path_t;
    pure function dma_route_root (bit_count : natural) return dma_route_path_t;

    pure function dma_route_junction (parent : dma_route_path_t; child_count : natural) return dma_route_junction_t;
    pure function dma_route_path (junc : dma_route_junction_t; child_index : natural) return dma_route_path_t;

    -- Modify routing metadata in request header for specific child of a junction
    pure function dma_route_req_apply_path (path : dma_route_path_t; dma_hdr : std_logic_vector) return std_logic_vector;
    -- Obtain routing value/vector of the current junction for response header
    pure function dma_route_res_extract_switch (junc : dma_route_junction_t; dma_hdr : std_logic_vector) return std_logic_vector;

    type dma_route_path_array_t is array (natural range <>) of dma_route_path_t;
    type dma_route_junction_array_t is array (natural range <>) of dma_route_junction_t;

    pure function dma_route_path_array_default (size : NATURAL) return dma_route_path_array_t;

    pure function dma_bus_get_payload_bit (dma_hdr : std_logic_vector) return std_logic;

end package;

-- ----------------------------------------------------------------------------
--                        DMA BUS package body
-- ----------------------------------------------------------------------------

package body dma_bus_pack is

    pure function dma_route_root (bit_count : natural) return dma_route_path_t is
        variable path : dma_route_path_t;
    begin
        path.routing_bit    := bit_count;
        path.siblings_count := 1;
        path.child_index    := 0;
        return path;
    end function;

    pure function dma_route_junction (parent : dma_route_path_t; child_count : natural) return dma_route_junction_t is
        constant BITS_NEEDED    : natural := log2(child_count);
        variable junc           : dma_route_junction_t;
    begin
        -- A junction with a single child does not need any routing bits.
        if (BITS_NEEDED = 0) then
            junc.routing_bit    := parent.routing_bit;
            junc.child_count    := child_count;
            return junc;
        end if;

        assert parent.routing_bit >= BITS_NEEDED - 1
            report "dma_route_junction: insufficient routing bits - cannot split "
                   & integer'image(child_count) & " children at depth "
                   & integer'image(parent.routing_bit)
            severity failure;

        -- Reserve the highest free bit for this junction.
        junc.routing_bit := parent.routing_bit - BITS_NEEDED;
        junc.child_count := child_count;

        return junc;
    end function;

    pure function dma_route_path (junc : dma_route_junction_t; child_index : natural) return dma_route_path_t is
        variable path : dma_route_path_t;
    begin
        path.routing_bit    := junc.routing_bit;
        path.siblings_count := junc.child_count;
        path.child_index    := child_index;
        return path;
    end function;

    pure function dma_route_res_extract_switch (junc : dma_route_junction_t; dma_hdr : std_logic_vector)
            return std_logic_vector is
        constant BITS_NEEDED    : natural := log2(junc.child_count);

        variable hdr_shifted    : std_logic_vector(dma_hdr'length-1 downto 0);
        variable unitid         : std_logic_vector(DMA_COMPLETION_UNITID_W-1 downto 0);
        variable ret            : std_logic_vector(BITS_NEEDED-1 downto 0);
        variable low_idx        : natural;
        variable high_idx       : natural;
    begin
        hdr_shifted := dma_hdr;     -- align low index to 0
        unitid      := hdr_shifted(DMA_COMPLETION_UNITID);

        if (BITS_NEEDED = 0) then
            ret := (0 downto 1 => '0');
            return ret;
        end if;

        high_idx := junc.routing_bit + BITS_NEEDED - 1;
        low_idx  := junc.routing_bit;

        ret := unitid(high_idx downto low_idx);
        return ret;
    end function;

    pure function dma_route_req_apply_path (path : dma_route_path_t; dma_hdr : std_logic_vector)
            return std_logic_vector is
        constant BITS_NEEDED    : natural := log2(path.siblings_count);

        variable hdr_shifted    : std_logic_vector(dma_hdr'length-1 downto 0);
        variable child_vec      : std_logic_vector(BITS_NEEDED-1 downto 0);
        variable high_idx       : natural;
        variable low_idx        : natural;
    begin
        hdr_shifted := dma_hdr;

        if (BITS_NEEDED = 0) then
            return hdr_shifted;
        end if;

        high_idx    := path.routing_bit + BITS_NEEDED - 1;
        low_idx     := path.routing_bit;

        -- Insert the new child index (binary, LSB‑aligned)
        child_vec   := std_logic_vector(to_unsigned(path.child_index, BITS_NEEDED));

        hdr_shifted(DMA_REQUEST_UNITID_O + high_idx downto DMA_REQUEST_UNITID_O + low_idx) := child_vec;

        return hdr_shifted;
    end function;

    pure function dma_route_path_default return dma_route_path_t is
    begin
        return dma_route_root(DMA_REQUEST_UNITID_W);
    end function;

    pure function dma_route_path_array_default (SIZE : natural) return dma_route_path_array_t is
        variable ret : dma_route_path_array_t(0 to SIZE-1);
    begin
        for i in 0 to SIZE-1 loop
            ret(i) := dma_route_path_default;
        end loop;
        return ret;
    end function;

    pure function dma_bus_get_payload_bit (dma_hdr : std_logic_vector) return std_logic is
        variable dma_hdr_shifted : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);
    begin
        dma_hdr_shifted := dma_hdr; -- Shift, so that the dma_hdr_shifted'low == 0 and the indexing works correctly
        if (dma_hdr_shifted(DMA_REQUEST_TYPE) = DMA_TYPE_WRITE) then
            return '1';
        else
            return '0';
        end if;
    end function;

end package body;
