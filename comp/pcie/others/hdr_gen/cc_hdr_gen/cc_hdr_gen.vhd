-- pcie_cc_hdr_gen.vhd: HDR generator for Completer
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

-- The Purpose of this component is to fill PCIE CC header.
entity PCIE_CC_HDR_GEN is
    generic (
        -- Target device: "AGILEX", "STRATIX10", "7SERIES", "ULTRASCALE"
        DEVICE         : string  := "STRATIX10"
    );
    port(
        -- ===================================
        -- CC interface (same fo both)
        -- ===================================

        -- Lower address
        IN_LOWER_ADDR   : in std_logic_vector(7-1 downto 0);
        -- Length in bytes (For Intel, only 12 bits are valid)
        IN_BYTE_CNT     : in std_logic_vector(13-1 downto 0);
        -- Length in DWORDS
        IN_DW_CNT       : in std_logic_vector(11-1 downto 0);
        -- Completition Status
        IN_COMP_ST      : in std_logic_vector(3-1 downto 0);
        -- Request ID
        IN_REQ_ID       : in std_logic_vector(16-1 downto 0);
        -- Tag (in case of INTEL contains TAG_8, TAG_9, TAG, others there is "00", TAG)
        IN_TAG          : in std_logic_vector(10-1 downto 0);
        -- Transaction Class
        IN_TC           : in std_logic_vector(3-1 downto 0);
        -- Contains snoop, relaxed and ID based ordering bit
        IN_ATTRIBUTES   : in std_logic_vector(3-1 downto 0);
        -- Global address type
        IN_ADDRESS_TYPE : in std_logic_vector(2-1 downto 0);
        -- Meta function ID
        IN_META_FUNC_ID : in std_logic_vector(8-1 downto 0);
        -- Bus number
        IN_BUS_NUM      : in std_logic_vector(8-1 downto 0);
        -- Type of completition:
        -- 1 - Completition with data
        -- 0 - completition without data
        COMP_WITH_DATA  : in std_logic;

        -- ===================================
        -- Completer HEADER Output interface
        -- ===================================

        -- PCIE CC header
        OUT_HEADER      : out std_logic_vector(96-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PCIE_CC_HDR_GEN is
    signal byte_count_intel : std_logic_vector(12-1 downto 0);
    signal in_tlp_type      : std_logic_vector(8-1 downto 0);
begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "PCIE_CC_HDR_GEN: unsupported device!" severity failure;

   -- -------------------------------------------------------------------------
   -- CC Header construction
   -- -------------------------------------------------------------------------

    cc_hdr_xilinx_g: if (DEVICE="ULTRASCALE" or DEVICE="7SERIES") generate
        OUT_HEADER <=
            '0'                & -- force ECRC
            IN_ATTRIBUTES      & -- attributes
            IN_TC              & -- transaction class
            '0'                & -- completer ID enable
            IN_BUS_NUM         & -- completer bus number
            IN_META_FUNC_ID    & -- target function/device number
            IN_TAG(7 downto 0) & -- tag
            IN_REQ_ID          & -- requester ID
            '0'                & -- RESERVED
            '0'                & -- poisoned completion
            IN_COMP_ST         & -- completion status
            IN_DW_CNT          & -- Dword count
            "00"               & -- RESERVED
            '0'                & -- locked read completion
            IN_BYTE_CNT        & -- byte count
            "000000"           & -- RESERVED
            IN_ADDRESS_TYPE    & -- address type
            '0'                & -- RESERVED
            IN_LOWER_ADDR;       -- lower address
    end generate;

    cc_hdr_intel_g: if (DEVICE="STRATIX10" or DEVICE="AGILEX") generate
        byte_count_intel <= std_logic_vector(resize(unsigned(IN_BYTE_CNT),12));

        in_tlp_type <= "01001010" when (COMP_WITH_DATA = '1') else "00001010";

        OUT_HEADER <=
            IN_REQ_ID                    & -- Requester ID
            IN_TAG(7 downto 0)           & -- Tag[7:0]
            '0'                          & -- reserved bit
            IN_LOWER_ADDR                & -- lower address
            IN_BUS_NUM & IN_META_FUNC_ID & -- completer ID (Bus number|META_FUNC_ID(Device number|Function number))
            IN_COMP_ST                   & -- completion status
            '0'                          & -- reserved bit
            byte_count_intel             & -- byte count
            in_tlp_type                  & -- fmt & type (only Completion with Data is supported)
            IN_TAG(9)                    & -- Tag[9] in PCIe Gen4 else reserved bit
            IN_TC                        & -- transaction class
            IN_TAG(8)                    & -- Tag[8] in PCIe Gen4 else reserved bit
            IN_ATTRIBUTES(2)             & -- attributes[2]
            "0000"                       & -- reserved bits
            IN_ATTRIBUTES(1 downto 0)    & -- attributes[1:0]
            IN_ADDRESS_TYPE              & -- address type
            IN_DW_CNT(9 downto 0);         -- dword count
    end generate;

end architecture;

