-- pcie_rc_hdr_deparser.vhd: HDR generator for Completer
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

-- The Purpose of this component is to deparse PCIE RC header.
entity PCIE_RC_HDR_DEPARSER is
    generic (
        -- Target device: "AGILEX", "STRATIX10", "7SERIES", "ULTRASCALE"
        DEVICE : string  := "STRATIX10"
    );
    port(
        -- ===================================
        -- RC interface
        -- ===================================

        -- Lower address
        OUT_LOW_ADDR   : out std_logic_vector(12-1 downto 0);
        -- Complete status
        OUT_COMPLETE   : out std_logic;
        -- Length in DWORDS
        OUT_DW_CNT     : out std_logic_vector(11-1 downto 0);
        -- Tag (in case of INTEL contains TAG_8, TAG_9, TAG, others there is "00", TAG)
        OUT_TAG        : out std_logic_vector(10-1 downto 0);
        -- Length in bytes (For Intel, only 12 bits are valid)
        OUT_BYTE_CNT   : out std_logic_vector(13-1 downto 0);
        -- Contains snoop (bit 0), relaxed (bit 1) and ID based ordering bit (bit 2)
        OUT_ATTRIBUTES : out std_logic_vector(3-1 downto 0);
        -- Completition Status
        OUT_COMP_ST    : out std_logic_vector(3-1 downto 0);
        -- ===================================
        -- Completer HEADER Input interface
        -- ===================================

        -- PCIE RC header
        IN_HEADER      : in std_logic_vector(96-1 downto 0)
    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PCIE_RC_HDR_DEPARSER is
    constant REMAINING_BYTES_WIDTH : natural := 12;
    signal rem_bytes_all : unsigned(REMAINING_BYTES_WIDTH-1 downto 0);
    signal rem_bytes_vld : unsigned(REMAINING_BYTES_WIDTH-1 downto 0);
begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "PCIE_RC_HDR_DEPARSER: unsupported device!" severity failure;

   -- -------------------------------------------------------------------------
   -- RC Header deparsing
   -- -------------------------------------------------------------------------

    cc_hdr_xilinx_g: if (DEVICE="ULTRASCALE" or DEVICE="7SERIES") generate
        OUT_LOW_ADDR   <=        IN_HEADER(12   -1 downto 0);
        OUT_BYTE_CNT   <=        IN_HEADER(29   -1 downto 16);
        OUT_COMPLETE   <=        IN_HEADER(30);
        OUT_DW_CNT     <=        IN_HEADER(32+11-1 downto 32);
        OUT_TAG        <= "00" & IN_HEADER(64+8 -1 downto 64);
        OUT_ATTRIBUTES <=        IN_HEADER(95   -1 downto 92);
        OUT_COMP_ST    <=        IN_HEADER(46   -1 downto 43);
    end generate;

    cc_hdr_intel_g: if (DEVICE="STRATIX10" or DEVICE="AGILEX") generate
        OUT_LOW_ADDR   <= "00000" & IN_HEADER(7+64                          -1 downto 64);
        OUT_DW_CNT     <= "0"     & IN_HEADER(10                            -1 downto 0);
        OUT_TAG        <=           IN_HEADER(23) & IN_HEADER(19) & IN_HEADER(72+8-1 downto 72);
        OUT_ATTRIBUTES <=           IN_HEADER(19-1) & IN_HEADER(14-1 downto 12);
        OUT_COMP_ST    <=           IN_HEADER(48-1 downto 45);

        -- Numer of remaining VALID bytes (according to request BE)
        OUT_BYTE_CNT   <= "0" & IN_HEADER(REMAINING_BYTES_WIDTH+32-1 downto 32);
        -- Numer of remaining bytes (including those disabled by request BE)
        rem_bytes_all  <= round_up(unsigned(OUT_BYTE_CNT(11 downto 0))+unsigned(OUT_LOW_ADDR(2-1 downto 0)),log2(4));
        --                '1' when (dword count in all remaining completion parts (including bytes disabled by BE))=(dword count in this completion part) else '0';
        OUT_COMPLETE   <= '1' when (std_logic_vector(rem_bytes_all(REMAINING_BYTES_WIDTH-1 downto 2)) )=(OUT_DW_CNT(10-1 downto 0)) else '0';
    end generate;

end architecture;

