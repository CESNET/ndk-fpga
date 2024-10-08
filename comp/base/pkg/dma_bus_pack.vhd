-- dma_bus_pack.vhd: DMA Bus Package
-- Copyright (C) 2017 CESNET
-- Author: Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

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

end dma_bus_pack;

-- ----------------------------------------------------------------------------
--                        DMA BUS package body
-- ----------------------------------------------------------------------------

package body dma_bus_pack is

end dma_bus_pack;

