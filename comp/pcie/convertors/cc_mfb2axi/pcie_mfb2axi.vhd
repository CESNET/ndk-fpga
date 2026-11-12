-- pcie_mfb2axi.vhd: Convertor from PCIE MFB CC to AXI interface
-- Copyright (C) 2022 CESNET
-- Author(s): Daniel Kriz <danielkriz@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The Purpose of this component is to convert MFB to AXI bus.
-- Supported is only 512b variant without straddling
entity PCIE_CC_MFB2AXI is
    generic (
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        --
        -- Supported configuration is: (4,1,8,32), (2,1,8,32), (1,1,8,32)
        -- =======================================================================
        MFB_REGIONS       : natural := 2;
        MFB_REGION_SIZE   : natural := 1;
        MFB_BLOCK_SIZE    : natural := 8;
        MFB_ITEM_WIDTH    : natural := 32;
        -- MFB bus: width of single data region in bits, auxiliary parameter, do not change value!
        MFB_REGION_WIDTH  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
        -- =======================================================================
        -- AXI BUS CONFIGURATION:
        --
        -- CC_USER_WIDTH = 165 for Gen4x16 and Gen5x8 PCIe - without straddling!
        -- CC_USER_WIDTH = 81 for Gen3x16 PCIe - without straddling
        -- CC_USER_WIDTH = 81 for Gen3x16 PCIe - with straddling
        -- CC_USER_WIDTH = 33 for Gen3x8 PCIe - without straddling
        -- =======================================================================
        AXI_CCUSER_WIDTH  : natural := 81;
        AXI_DATA_WIDTH    : natural := 512;
        -- Not supported
        STRADDLING        : boolean := false

    );
    port (

        -- =====================================================================
        -- MFB Completer Request Interface (CC) - Intel FPGA Only
        -- =====================================================================

        -- CC_MFB: data word with frames (packets)
        CC_MFB_DATA       : in  std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        -- CC_MFB: Start Of Frame (SOF) flag for each MFB region
        CC_MFB_SOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CC_MFB: End Of Frame (EOF) flag for each MFB region
        CC_MFB_EOF        : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CC_MFB: SOF position for each MFB region in MFB blocks
        CC_MFB_SOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        -- CC_MFB: EOF position for each MFB region in MFB items
        CC_MFB_EOF_POS    : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- CC_MFB: source ready of each MFB bus
        CC_MFB_SRC_RDY    : in  std_logic;
        -- CC_MFB: destination ready of each MFB bus
        CC_MFB_DST_RDY    : out std_logic;

        -- =====================================================================
        -- AXI Completer Request Interface (CC) - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================

        -- CC_AXI: Data word. For detailed specifications, see Xilinx PG213.
        CC_AXI_DATA       : out  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        -- CC_AXI: Set of signals with sideband information about trasferred
        -- transaction. For detailed specifications, see Xilinx PG213.
        CC_AXI_USER       : out  std_logic_vector(AXI_CCUSER_WIDTH-1 downto 0);
        -- CC_AXI: Indication of the last word of a transaction. For detailed
        -- specifications, see Xilinx PG213.
        CC_AXI_LAST       : out  std_logic;
        -- CC_AXI: Indication of valid data: each bit determines validity of
        -- different Dword. For detailed specifications, see Xilinx PG213.
        CC_AXI_KEEP       : out  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        -- CC_AXI: Indication of valid data: i.e. completer is ready to send a
        -- transaction. For detailed specifications, see Xilinx PG213.
        CC_AXI_VALID      : out  std_logic;
        -- CC_AXI: User application is ready to receive a transaction.
        -- For detailed specifications, see Xilinx PG213.
        CC_AXI_READY      : in std_logic

    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------
architecture FULL of PCIE_CC_MFB2AXI is
    constant EOP_POS_WIDTH : integer := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    signal cc_keep         : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
    signal cc_user         : std_logic_vector(AXI_CCUSER_WIDTH -1 downto 0);

    signal cc_usr_sop     : std_logic_vector(1 downto 0);
    signal cc_usr_eop     : std_logic_vector(1 downto 0);
    signal cc_usr_sop_ptr : slv_array_t(1 downto 0)(1 downto 0);
    signal cc_usr_eop_ptr : slv_array_t(1 downto 0)(3 downto 0);
begin
    assert ((MFB_REGIONS = 1 and AXI_CCUSER_WIDTH = 33 and not STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CCUSER_WIDTH = 81 and STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CCUSER_WIDTH = 81 and not STRADDLING)
            or (MFB_REGIONS = 4 and AXI_CCUSER_WIDTH = 165 and not STRADDLING))
        report "PCIE_CC_MFB2AXI: Unsupported AXI CC USER port width, the supported are: 33 (when MFB_REGIONS = 1), 81 (when MFB_REGIONS = 2), 165 (when MFB_REGIONS = 4)"
        severity FAILURE;

    no_straddling_g : if not STRADDLING generate
        constant REGION_DWORDS : natural := AXI_DATA_WIDTH/32/MFB_REGIONS;
    begin
        assert ((AXI_DATA_WIDTH/32) mod MFB_REGIONS = 0)
            report "PCIE_CC_MFB2AXI: AXI_DATA_WIDTH/32 must be divisible by MFB_REGIONS!"
            severity failure;

        -- The component has no clock, so this is not a clocked PSL assertion.
        assert (CC_MFB_SRC_RDY /= '1' or count_ones(CC_MFB_EOF) <= 1)
            report "PCIE_CC_MFB2AXI: More than one EOF in a word, straddling is disabled!"
            severity failure;

        cc_user <= (others => '0');

        -- Dwords up to the end of the frame are valid, all of them in a word without EOF.
        -- With several EOFs (an assertion failure) the lowest region wins as before.
        s_cc_keep_pr : process (all) is
            variable eof_pos   : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_POS_WIDTH-1 downto 0);
            variable end_dword : natural range 0 to AXI_DATA_WIDTH/32-1;
        begin
            eof_pos   := slv_array_deser(CC_MFB_EOF_POS, MFB_REGIONS);
            end_dword := AXI_DATA_WIDTH/32-1;
            for r in MFB_REGIONS-1 downto 0 loop
                if (CC_MFB_EOF(r) = '1') then
                    end_dword := r*REGION_DWORDS + to_integer(unsigned(eof_pos(r)));
                end if;
            end loop;

            for i in cc_keep'range loop
                cc_keep(i) <= '1' when (i <= end_dword) else '0';
            end loop;
        end process;
    else generate
        cc_keep <= (others => '0');

        s_cc_user_signal_assign_p : process (all) is
        begin
            cc_usr_sop     <= (others => '0');
            cc_usr_sop_ptr <= (others => (others => '0'));
            cc_usr_eop     <= (others => '0');
            cc_usr_eop_ptr <= (others => (others => '0'));

            -- Only one TLP starts in this beat
            if (CC_MFB_SOF = "01") then
                cc_usr_sop        <= "01";
                cc_usr_sop_ptr(0) <= "00";

            -- This is an unallowed combination and is only there for the completeness
            elsif (CC_MFB_SOF = "10") then
                cc_usr_sop        <= "01";
                cc_usr_sop_ptr(0) <= "10";

            -- Two TLPs start in this beat
            elsif (CC_MFB_SOF = "11") then
                cc_usr_sop        <= "11";
                cc_usr_sop_ptr(0) <= "00";
                cc_usr_sop_ptr(1) <= "10";
            end if;

            -- One TLP ends in this beat and in the first region
            if (CC_MFB_EOF = "01") then
                cc_usr_eop        <= "01";
                cc_usr_eop_ptr(0) <= "0" & CC_MFB_EOF_POS(2 downto 0);

            -- One TLP ends in this beat and in the second region
            elsif (CC_MFB_EOF = "10") then
                cc_usr_eop        <= "01";
                cc_usr_eop_ptr(0) <= "1" & CC_MFB_EOF_POS(5 downto 3);

            -- Two TLPs end in this beat
            elsif (CC_MFB_EOF = "11") then
                cc_usr_eop        <= "11";
                cc_usr_eop_ptr(0) <= "0" & CC_MFB_EOF_POS(2 downto 0);
                cc_usr_eop_ptr(1) <= "1" & CC_MFB_EOF_POS(5 downto 3);
            end if;
        end process;

        cc_user <= (64 downto 0 => '0')
                   & cc_usr_eop_ptr(1)
                   & cc_usr_eop_ptr(0)
                   & cc_usr_eop
                   & cc_usr_sop_ptr(1)
                   & cc_usr_sop_ptr(0)
                   & cc_usr_sop;
    end generate;

    CC_AXI_DATA    <= CC_MFB_DATA;
    CC_AXI_KEEP    <= cc_keep;
    CC_AXI_USER    <= cc_user;
    CC_AXI_LAST    <= or CC_MFB_EOF;
    CC_AXI_VALID   <= CC_MFB_SRC_RDY;
    CC_MFB_DST_RDY <= CC_AXI_READY;

end architecture;
