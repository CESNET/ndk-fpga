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
    generic(
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        --
        -- Supported configuration is: (2,1,8,32), (1,1,8,32)
        -- =======================================================================
        MFB_REGIONS      : natural := 2;
        MFB_REGION_SIZE  : natural := 1;
        MFB_BLOCK_SIZE   : natural := 8;
        MFB_ITEM_WIDTH   : natural := 32;
        -- MFB bus: width of single data region in bits, auxiliary parameter, do not change value!
        MFB_REGION_WIDTH  : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
        -- =======================================================================
        -- AXI BUS CONFIGURATION:
        --
        -- CC_USER_WIDTH = 81 for Gen3x16 PCIe - without straddling!
        -- CC_USER_WIDTH = 33 for Gen3x8 PCIe - without straddling!
        -- =======================================================================
        AXI_CCUSER_WIDTH : natural := 81;
        AXI_DATA_WIDTH   : natural := 512;
        -- Not supported
        STRADDLING       : boolean := false

        );
    port(

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
architecture full of PCIE_CC_MFB2AXI is
    constant EOP_POS_WIDTH : integer := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    signal cc_keep         : std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
begin
    assert (AXI_CCUSER_WIDTH = 33 or AXI_CCUSER_WIDTH = 81)
    report "PCIE_CC_MFB2AXI: Unsupported AXI CC USER port width, the supported are: 33, 81"
        severity FAILURE;

        -- No straddling supported!
        -- keep signal serves as valid for each DWORD of CC_AXI_DATA signal
        axi_512b_g: if (MFB_REGIONS = 2) generate
        s_cc_keep_pr : process (all)
            begin
                if (CC_MFB_EOF(0) = '1') then -- end of data in first region
                    cc_keep <= (others => '0');

                    for i in 0 to AXI_DATA_WIDTH/32-1 loop
                        cc_keep(i) <= '1';
                        exit when (i = to_integer(unsigned(CC_MFB_EOF_POS(EOP_POS_WIDTH-1 downto 0))));
                    end loop;

                elsif (CC_MFB_EOF(1) = '1') then -- end of data in second region
                    cc_keep <= (others => '0');

                    for i in 0 to AXI_DATA_WIDTH/32-1 loop
                        cc_keep(i) <= '1';
                        exit when (i = ((AXI_DATA_WIDTH/32)/2) + to_integer(unsigned(CC_MFB_EOF_POS(2*EOP_POS_WIDTH-1 downto EOP_POS_WIDTH))));
                    end loop;

                else -- start or middle of data
                    cc_keep <= (others => '1');
                end if;
            end process;
    else generate
        s_cc_keep_pr : process (all)
        begin
            if (CC_MFB_EOF(0) = '1') then -- end of data in first region
                cc_keep <= (others => '0');

                for i in 0 to AXI_DATA_WIDTH/32-1 loop
                    cc_keep(i) <= '1';
                    exit when (i = to_integer(unsigned(CC_MFB_EOF_POS(EOP_POS_WIDTH-1 downto 0))));
                end loop;
            else -- start or middle of data
                cc_keep <= (others => '1');
            end if;
        end process;
    end generate;

    CC_AXI_DATA    <= CC_MFB_DATA;
    CC_AXI_KEEP    <= cc_keep;
    CC_AXI_USER    <= (others => '0');
    CC_AXI_LAST    <= or CC_MFB_EOF;
    CC_AXI_VALID   <= CC_MFB_SRC_RDY;
    CC_MFB_DST_RDY <= CC_AXI_READY;

end architecture;
