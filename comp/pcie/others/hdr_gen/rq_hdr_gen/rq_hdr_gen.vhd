-- pcie_rq_hdr_gen.vhd: HDR generator for Requester
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

-- The Purpose of this component is to fill PCIE RQ header.
entity PCIE_RQ_HDR_GEN is
    generic (
        -- Target device: "AGILEX", "STRATIX10", "7SERIES", "ULTRASCALE"
        DEVICE        : string  := "STRATIX10"
    );
    port(
        -- ===================================
        -- RQ interface
        -- ===================================

        -- Global address in bytes (address is aligned in DWORD)
        IN_ADDRESS       : in std_logic_vector(62-1 downto 0);
        -- Virtual Function ID
        IN_VFID          : in std_logic_vector(8-1 downto 0);
        -- Tag (in case of INTEL contains: TAG_8, TAG_9, TAG, others there is "00", TAG)
        IN_TAG           : in std_logic_vector(10-1 downto 0);
        -- Length in DWORDS
        IN_DW_CNT        : in std_logic_vector(11-1 downto 0);
        -- Contains snoop (bit 0), relaxed (bit 1) and ID based ordering bit (bit 2)
        IN_ATTRIBUTES    : in std_logic_vector(3-1 downto 0);
        -- First Byte Enable (Intel only)
        IN_FBE           : in std_logic_vector(4-1 downto 0) := (others => '0');
        -- Last Byte Enable (Intel only)
        IN_LBE           : in std_logic_vector(4-1 downto 0) := (others => '0');
        -- Address length type, supported are:
        -- 1 - 64-DW address
        -- 0 - 32-DW address
        IN_ADDR_LEN      : in std_logic;
        -- Type of request, supported types are:
        -- 1 - write
        -- 0 - read
        IN_REQ_TYPE      : in std_logic;

        -- ===================================
        -- Requester HEADER Output interface
        -- ===================================

        -- PCIE RQ header
        OUT_HEADER   : out std_logic_vector(128-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PCIE_RQ_HDR_GEN is

begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "PCIE_RQ_HDR_GEN: unsupported device!" severity failure;

   -- -------------------------------------------------------------------------
   -- RQ PCIE Header construction
   -- -------------------------------------------------------------------------

    xilinx_pcie_hdr_gen : if (DEVICE="ULTRASCALE" or DEVICE="7SERIES") generate

        OUT_HEADER <=
            '0'                        & -- force ECRC
            IN_ATTRIBUTES              & -- attributes
            "000"                      & -- transaction class
            '0'                        & -- requester ID enable
            X"0000"                    & -- completer ID
            IN_TAG(7 downto 0)         & -- tag
            X"00" & IN_VFID            & -- requester ID
            '0'                        & -- poisoned request
            "000" & IN_REQ_TYPE        & -- request type
            IN_DW_CNT                  & -- Dword count
            IN_ADDRESS                 & -- address
            "00";                       -- address type

    end generate;

    intel_pcie_hdr_gen : if (DEVICE="STRATIX10" or DEVICE="AGILEX") generate

        OUT_HEADER <=
            -- 96 bit header type
            (32-1 downto 0 => '0')     & -- padding
            IN_ADDRESS(30-1 downto 0)  & -- lower address
            "00"                       & -- padding
            X"00" & IN_VFID            & -- requester ID
            IN_TAG(7 downto 0)         & -- tag
            IN_LBE                     & -- last byte enable
            IN_FBE                     & -- first byte enable
            '0' & IN_REQ_TYPE          & -- request type
            IN_ADDR_LEN                & -- 96 bit header type
            "00000"                    & -- padding
            IN_TAG(9)                  & -- bit 9 of tag
            "000"                      & -- priority
            IN_TAG(8)                  & -- bit 8 of tag
            IN_ATTRIBUTES(2) & "00"    & -- padding
            '0'                        & -- ECRC
            '0'                        & -- poisoned request
            IN_ATTRIBUTES(1 downto 0)  & -- relaxed bit & no snoop
            "00"                       & -- padding
            IN_DW_CNT(10-1 downto 0)     -- Dword count

        when IN_ADDR_LEN = '0' else

            -- 128 bit header type
            IN_ADDRESS(30-1 downto 0)  & -- lower address
            "00"                       & -- padding
            IN_ADDRESS(62-1 downto 30) & -- higher address
            X"00" & IN_VFID            & -- requester ID
            IN_TAG(7 downto 0)         & -- tag
            IN_LBE                     & -- last byte enable
            IN_FBE                     & -- first byte enable
            '0' & IN_REQ_TYPE          & -- request type
            IN_ADDR_LEN                & -- 128 bit header type
            "00000"                    & -- padding
            IN_TAG(9)                  & -- bit 9 of tag
            "000"                      & -- priority
            IN_TAG(8)                  & -- bit 8 of tag
            IN_ATTRIBUTES(2) & "00"    & -- padding
            '0'                        & -- ECRC
            '0'                        & -- poisoned request
            IN_ATTRIBUTES(1 downto 0)  & -- relaxed bit & no snoop
            "00"                       & -- padding
            IN_DW_CNT(10-1 downto 0);    -- Dword count

    end generate;

end architecture;

