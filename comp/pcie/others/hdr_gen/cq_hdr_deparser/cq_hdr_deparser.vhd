-- pcie_cq_hdr_deparser.vhd: CQ HDR deparser
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

-- The Purpose of this component is to deparse PCIE CQ header.
entity PCIE_CQ_HDR_DEPARSER is
    generic (
        -- Target device: "AGILEX", "STRATIX10", "7SERIES", "ULTRASCALE"
        DEVICE       : string  := "STRATIX10";
        -- width of CQ user word in bits (Supported value are 88, 85 and 183)
        CQUSER_WIDTH : natural := 183
    );
    port(
        -- ========================================================================
        -- CQ interface (same for both)
        -- ========================================================================

        -- Tag (in case of INTEL contains TAG_8, TAG_9, TAG, others there is "00", TAG)
        OUT_TAG          : out std_logic_vector(10-1 downto 0);
        -- Global address in bytes (address is aligned to DWORD)
        OUT_ADDRESS      : out std_logic_vector(64-1 downto 0);
        -- Request ID
        OUT_REQ_ID       : out std_logic_vector(16-1 downto 0);
        -- Transaction Class
        OUT_TC           : out std_logic_vector(3-1 downto 0);
        -- Length in DWORDS
        OUT_DW_CNT       : out std_logic_vector(11-1 downto 0);
        -- Contains snoop, relaxed and ID based ordering bit
        OUT_ATTRIBUTES   : out std_logic_vector(3-1 downto 0);
        -- First Byte Enable
        OUT_FBE          : out std_logic_vector(4-1 downto 0);
        -- Last Byte Enable
        OUT_LBE          : out std_logic_vector(4-1 downto 0);
        -- Global address type
        OUT_ADDRESS_TYPE : out std_logic_vector(2-1 downto 0);
        -- Target function (META_FUNC_ID)
        OUT_TARGET_FUNC  : out std_logic_vector(8-1 downto 0);
        -- BAR ID
        OUT_BAR_ID       : out std_logic_vector(3-1 downto 0);
        -- BAR APERTURE
        OUT_BAR_APERTURE : out std_logic_vector(6-1 downto 0);
        -- Address length type, supported are:
        -- 1 - 64-DW address
        -- 0 - 32-DW address
        OUT_ADDR_LEN     : out std_logic;
        -- Type of request, supported types are:
        -- 0000 - others
        -- 0001 - read
        -- 0010 - write
        -- 0100 - msg
        -- 1000 - msgd
        OUT_REQ_TYPE     : out std_logic_vector(4-1 downto 0);

        -- ========================================================================
        -- Completer HEADER Input interface
        -- ========================================================================

        -- PCIE AXI TUSER signal
        IN_AXI_TUSER     : in std_logic_vector(CQUSER_WIDTH-1 downto 0) := (others => '0');
        -- PCIE CQ header
        IN_HEADER        : in std_logic_vector(128-1 downto 0);
        -- First Byte Enable
        IN_FBE           : in std_logic_vector(4-1 downto 0);
        -- Last Byte Enable
        IN_LBE           : in std_logic_vector(4-1 downto 0);
        -- PCIE CQ header META, contains: BAR_APERTURE, BAR_ID, TARGET_FUNC
        IN_INTEL_META    : in std_logic_vector(17-1 downto 0) := (others => '0')
    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PCIE_CQ_HDR_DEPARSER is
    signal cq_addr32 : std_logic_vector(62-1 downto 0);
    signal cq_addr64 : std_logic_vector(62-1 downto 0);
begin

    assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
        report "PCIE_CQ_HDR_DEPARSER: unsupported device!" severity failure;

   -- -------------------------------------------------------------------------
   -- CQ Header deparsing
   -- -------------------------------------------------------------------------

    cq_hdr_xilinx_g: if (DEVICE="ULTRASCALE" or DEVICE="7SERIES") generate
        OUT_ADDRESS_TYPE <= IN_HEADER(1 downto 0);
        OUT_ADDRESS      <= IN_HEADER(63 downto 2) & "00";
        OUT_DW_CNT       <= IN_HEADER(74 downto 64);
        OUT_REQ_ID       <= IN_HEADER(95 downto 80);
        OUT_TAG          <= "00" & IN_HEADER(103 downto 96);
        OUT_TARGET_FUNC  <= IN_HEADER(111 downto 104);
        OUT_BAR_ID       <= IN_HEADER(114 downto 112);
        OUT_BAR_APERTURE <= IN_HEADER(120 downto 115);
        OUT_TC           <= IN_HEADER(123 downto 121);
        OUT_ATTRIBUTES   <= IN_HEADER(126 downto 124);
        OUT_FBE          <= IN_FBE;
        OUT_LBE          <= IN_LBE;

        OUT_REQ_TYPE(0) <= '1' when (unsigned(IN_HEADER(78 downto 75)) = 0) else '0';
        OUT_REQ_TYPE(1) <= '1' when (unsigned(IN_HEADER(78 downto 75)) = 1) else '0';
        OUT_REQ_TYPE(3 downto 2) <= "00";
        OUT_ADDR_LEN <= '1';
    end generate;

    cq_hdr_intel_g: if (DEVICE="STRATIX10" or DEVICE="AGILEX") generate
        OUT_DW_CNT       <= '0' & IN_HEADER(9 downto 0);
        OUT_ADDRESS_TYPE <= IN_HEADER(11 downto 10);
        OUT_ATTRIBUTES   <= IN_HEADER(18) & IN_HEADER(13 downto 12);
        OUT_TAG          <= IN_HEADER(23) & IN_HEADER(19) & IN_HEADER(47 downto 40);
        OUT_TC           <= IN_HEADER(22 downto 20);
        OUT_FBE          <= IN_HEADER(35 downto 32);
        OUT_LBE          <= IN_HEADER(39 downto 36);
        OUT_REQ_ID       <= IN_HEADER(63 downto 48);
        cq_addr32        <= std_logic_vector(to_unsigned(0,32)) & IN_HEADER(95 downto 66);
        cq_addr64        <= IN_HEADER(95 downto 64) & IN_HEADER(127 downto 98);
        OUT_ADDRESS      <= (cq_addr64 & "00") when (IN_HEADER(29) = '1') else
                            (cq_addr32 & "00");
        OUT_TARGET_FUNC  <= IN_INTEL_META(7 downto 0);
        OUT_BAR_ID       <= IN_INTEL_META(10 downto 8);
        OUT_BAR_APERTURE <= IN_INTEL_META(16 downto 11);

        with IN_HEADER(31 downto 24) select
        OUT_REQ_TYPE(1 downto 0) <= "01" when "00000000", -- 32b mem rd
                                    "10" when "01000000", -- 32b mem wr
                                    "01" when "00100000", -- 64b mem rd
                                    "10" when "01100000", -- 64b mem wr
                                    "00" when others;

        with IN_HEADER(31 downto 27) select
        OUT_REQ_TYPE(3 downto 2) <= "01" when "00110", -- Msg
                                    "10" when "01110", -- MsgD
                                    "00" when others;

        OUT_ADDR_LEN <= IN_HEADER(29);
    end generate;

end architecture;

