-- pcie_axi2mfb.vhd: Convertor from AXI to PCIE CQ interface
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

-- The Purpose of this component is to convert AXI to MFB bus.
-- Supported are 512b and 256b with and without straddling, but
-- variants with straddling and all 256 variant has not been tested.
entity PCIE_CQ_AXI2MFB is
    generic (
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        --
        -- Supported configurations are: (2,1,8,32), (1,1,8,32)
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
        -- CQ_USER_WIDTH = 183 for Gen3x16 PCIe - with straddling and without straddling!
        -- CQ_USER_WIDTH = 88  for Gen3x8 PCIe - without straddling!
        -- CQ_USER_WIDTH = 85  for Gen3x8 PCIe - without straddling!
        -- =======================================================================

        AXI_CQUSER_WIDTH  : natural := 183;
        AXI_DATA_WIDTH    : natural := MFB_REGIONS*MFB_REGION_WIDTH;
        -- Straddling is permited only for CQ_USER_WIDTH = 183
        STRADDLING        : boolean := false;
        -- Select correct FPGA device: "ULTRASCALE", "VIRTEX7"
        DEVICE            : string := "ULTRASCALE"

    );
    port (

        -- =====================================================================
        -- AXI Completer Request Interface (CQ) - Xilinx FPGA Only
        --
        -- See Xilinx PG213 (UltraScale+ Devices Integrated Block for PCI Express).
        -- =====================================================================

        -- CQ_AXI: Data word. For detailed specifications, see Xilinx PG213.
        CQ_AXI_DATA       : in  std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
        -- CQ_AXI: Set of signals with sideband information about trasferred
        -- transaction. For detailed specifications, see Xilinx PG213.
        CQ_AXI_USER       : in  std_logic_vector(AXI_CQUSER_WIDTH-1 downto 0);
        -- CQ_AXI: Indication of the last word of a transaction. For detailed
        -- specifications, see Xilinx PG213.
        CQ_AXI_LAST       : in  std_logic;
        -- CQ_AXI: Indication of valid data: each bit determines validity of
        -- different Dword. For detailed specifications, see Xilinx PG213.
        CQ_AXI_KEEP       : in  std_logic_vector(AXI_DATA_WIDTH/32-1 downto 0);
        -- CQ_AXI: Indication of valid data: i.e. completer is ready to send a
        -- transaction. For detailed specifications, see Xilinx PG213.
        CQ_AXI_VALID      : in  std_logic;
        -- CQ_AXI: User application is ready to receive a transaction.
        -- For detailed specifications, see Xilinx PG213.
        CQ_AXI_READY      : out std_logic;

        -- =====================================================================
        -- MFB Completer Request Interface (CQ) - Intel FPGA Only
        -- =====================================================================

        -- CQ_MFB: data word with frames (packets)
        CQ_MFB_DATA       : out  std_logic_vector(MFB_REGIONS*MFB_REGION_WIDTH-1 downto 0);
        -- CQ_MFB: Start Of Frame (SOF) flag for each MFB region
        CQ_MFB_SOF        : out  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CQ_MFB: End Of Frame (EOF) flag for each MFB region
        CQ_MFB_EOF        : out  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- CQ_MFB: SOF position for each MFB region in MFB blocks
        CQ_MFB_SOF_POS    : out  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        -- CQ_MFB: EOF position for each MFB region in MFB items
        CQ_MFB_EOF_POS    : out  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        -- CQ_MFB: source ready of each MFB bus
        CQ_MFB_SRC_RDY    : out  std_logic;
        -- CQ_MFB: destination ready of each MFB bus
        CQ_MFB_DST_RDY    : in std_logic;

        -- =====================================================================
        -- CQ_AXI_USER SIGNAL ITEMS
        --
        -- Ports below are valid only with CQ_MFB_SOF
        -- =====================================================================

        -- This bit indicates presence of Transaction Processing Hint (TPH)
        CQ_TPH_PRESENT    : out std_logic_vector(MFB_REGIONS-1 downto 0);
        -- These two bits provide the value of the PH field associated with the hint
        CQ_TPH_TYPE       : out std_logic_vector(MFB_REGIONS*2-1 downto 0);
        -- This output provides the 8-bit Steering Tag associated with the hint
        CQ_TPH_ST_TAG     : out std_logic_vector(MFB_REGIONS*8-1 downto 0);
        -- Byte enables for the first DWORD
        CQ_FBE            : out std_logic_vector(MFB_REGIONS*4-1 downto 0);
        -- Byte enables for the last DWORD
        CQ_LBE            : out std_logic_vector(MFB_REGIONS*4-1 downto 0)

    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture FULL of PCIE_CQ_AXI2MFB is

    -- ========================================================================
    -- Constants
    -- ========================================================================

    constant SOF_POS_WIDTH     : integer := max(1,log2(MFB_REGION_SIZE));
    constant EOP_POS_WIDTH     : integer := max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    -- ========================================================================
    -- Signals
    -- ========================================================================

    signal cq_axi_pipe_din         : std_logic_vector(AXI_DATA_WIDTH+AXI_CQUSER_WIDTH+1-1 downto 0);
    signal cq_axi_pipe_dout        : std_logic_vector(AXI_DATA_WIDTH+AXI_CQUSER_WIDTH+1-1 downto 0);

    signal cq_axi_data_in          : std_logic_vector(AXI_DATA_WIDTH-1 downto 0);
    signal cq_axi_user_in          : std_logic_vector(AXI_CQUSER_WIDTH-1 downto 0);
    signal cq_axi_last_in          : std_logic;
    signal cq_axi_vld_in           : std_logic;
    signal cq_axi_ready_in         : std_logic;

    -- RX AXI TUSER division
    signal cq_axi_user_sop         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_axi_user_sop_ptr     : slv_array_t(MFB_REGIONS-1 downto 0)(2-1 downto 0);
    signal cq_axi_user_eop         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_axi_user_eop_ptr     : slv_array_t(MFB_REGIONS-1 downto 0)(4-1 downto 0);
    signal cq_axi_user_tph_present : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_axi_user_tph_type    : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal cq_axi_user_tph_st_tag  : std_logic_vector(MFB_REGIONS*8-1 downto 0);
    signal cq_axi_user_fbe         : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    signal cq_axi_user_lbe         : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    ---------------------------------------------------------------------------

begin
    assert ((MFB_REGIONS = 1 and (AXI_CQUSER_WIDTH = 85 or AXI_CQUSER_WIDTH = 88) and not STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 183 and STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 183 and not STRADDLING))
        report "PCIE_CQ_AXI2MFB: Unsupported AXI CQ USER port width, the supported are: 85 (MFB_REGIONS = 1), 88 (MFB_REGIONS = 1), 183 (MFB_REGIONS = 2)"
        severity FAILURE;

    -- =========================================================================
    -- Conversion AXI to MFB for ULTRASCALE and VIRTEX7 256b variant:
    --
    -- Has not been tested
    -- =========================================================================

    axi_256b_g: if (AXI_CQUSER_WIDTH = 88 or AXI_CQUSER_WIDTH = 85) generate
        cq_axi_user_sop(0)     <= CQ_AXI_USER(40);
        cq_axi_user_fbe        <= CQ_AXI_USER(4-1 downto 0);
        cq_axi_user_lbe        <= CQ_AXI_USER(8-1 downto 4);

        conv_256_pr : process (all)
            variable eof_pos   : unsigned(3-1 downto 0) := (others => '0');
            variable eof       : std_logic_vector(1 downto 0);
        begin
            eof_pos        := (others => '0');
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');
            CQ_MFB_EOF_POS <= (others => '0');

            if (cq_axi_user_sop(0) = '1') then
                CQ_TPH_PRESENT(0) <= CQ_AXI_USER(42);
                CQ_TPH_TYPE       <= CQ_AXI_USER(44 downto 43);
                CQ_TPH_ST_TAG     <= CQ_AXI_USER(52 downto 45);
            end if;

            if (CQ_AXI_LAST = '1') then

                for i in 0 to ((AXI_DATA_WIDTH/32)-1) loop
                    exit when (CQ_AXI_KEEP(i) = '0');
                    eof_pos := eof_pos + 1;
                end loop;

                CQ_MFB_EOF_POS(EOP_POS_WIDTH-1 downto 0) <= std_logic_vector((eof_pos-1));
            end if;

        end process;

        CQ_MFB_SOF     <= cq_axi_user_sop;
        CQ_MFB_SOF_POS <= (others => '0');
        CQ_MFB_EOF(0)  <= CQ_AXI_LAST;
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for ULTRASCALE 512b variant with straddling
    -- =========================================================================

    axi_512b_g: if (AXI_CQUSER_WIDTH = 183 and STRADDLING) generate
        cq_axi_user_sop         <= CQ_AXI_USER(81 downto 80);
        cq_axi_user_sop_ptr(0)  <= CQ_AXI_USER(83 downto 82);
        cq_axi_user_sop_ptr(1)  <= CQ_AXI_USER(85 downto 84);
        cq_axi_user_eop         <= CQ_AXI_USER(87 downto 86);
        cq_axi_user_eop_ptr(0)  <= CQ_AXI_USER(91 downto 88);
        cq_axi_user_eop_ptr(1)  <= CQ_AXI_USER(95 downto 92);

        -- conversion process
        sop_eop_sof_eof_conv_pr : process (all)
        begin
            -- default values
            CQ_MFB_SOF_POS <= (others => '0');
            CQ_MFB_EOF_POS <= (others => '0');
            CQ_MFB_SOF     <= (others => '0');
            CQ_MFB_EOF     <= (others => '0');
            CQ_TPH_PRESENT <= CQ_AXI_USER(98 downto 97);
            CQ_TPH_TYPE    <= CQ_AXI_USER(102 downto 99);
            CQ_TPH_ST_TAG  <= CQ_AXI_USER(118 downto 103);

            -- There is only one TLP in this beat
            if (cq_axi_user_sop = "01") then
                -- TLP Present in the second region
                if (cq_axi_user_sop_ptr(0) = "10") then
                    CQ_MFB_SOF <= "10";

                    CQ_TPH_PRESENT <= CQ_AXI_USER(97) & "0";
                    CQ_TPH_TYPE    <= CQ_AXI_USER(100 downto 99) & "00";
                    CQ_TPH_ST_TAG  <= CQ_AXI_USER(110 downto 103) & "00000000";
                -- TLP Present in the first region
                else
                    CQ_MFB_SOF <= "01";

                    CQ_TPH_PRESENT <= "0" & CQ_AXI_USER(97);
                    CQ_TPH_TYPE    <= "00" & CQ_AXI_USER(100 downto 99);
                    CQ_TPH_ST_TAG  <= "00000000" & CQ_AXI_USER(110 downto 103);
                end if;

            -- THere are 2 TLPs in this beat
            elsif (cq_axi_user_sop = "11") then
                CQ_MFB_SOF <= "11";
            end if;

            -- One TLP ends in this beat
            if (cq_axi_user_eop = "01") then
                -- The TLP ends in the first region
                if (unsigned(cq_axi_user_eop_ptr(0)) < 8) then
                    CQ_MFB_EOF     <= "01";
                    CQ_MFB_EOF_POS <= "000" & cq_axi_user_eop_ptr(0)(2 downto 0);

                -- The TLP ends in the second region
                else
                    CQ_MFB_EOF     <= "10";
                    CQ_MFB_EOF_POS <= cq_axi_user_eop_ptr(0)(2 downto 0) & "000";
                end if;

            -- Two TLPs end in this beat
            elsif (cq_axi_user_eop = "11") then
                CQ_MFB_EOF     <= "11";
                CQ_MFB_EOF_POS <= cq_axi_user_eop_ptr(1)(2 downto 0) & cq_axi_user_eop_ptr(0)(2 downto 0);
            end if;
        end process;
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for ULTRASCALE 512b variant
    -- =========================================================================

    axi_512b_no_straddling_g: if (AXI_CQUSER_WIDTH = 183 and not STRADDLING) generate
        cq_axi_user_tph_present <= CQ_AXI_USER(99-1 downto 97);
        cq_axi_user_tph_type    <= CQ_AXI_USER(103-1 downto 99);
        cq_axi_user_tph_st_tag  <= CQ_AXI_USER(119-1 downto 103);
        cq_axi_user_sop(0)      <= CQ_AXI_USER(80);
        cq_axi_user_sop(1)      <= '0';
        CQ_MFB_SOF              <= cq_axi_user_sop;
        CQ_MFB_SOF_POS          <= (others => '0');
        cq_axi_user_fbe         <= "0000" & CQ_AXI_USER(4-1 downto 0);
        cq_axi_user_lbe         <= "0000" & CQ_AXI_USER(12-1 downto 8);

        conv_pr : process (all)
            variable eof_pos : unsigned(3-1 downto 0) := (others => '0');
            variable eof     : std_logic_vector(1 downto 0);
        begin
            eof_pos        := (others => '0');
            eof            := (others => '0');
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');
            CQ_MFB_EOF     <= (others => '0');
            CQ_MFB_EOF_POS <= (others => '0');

            if (CQ_AXI_USER(80) = '1') then
                CQ_TPH_PRESENT <= cq_axi_user_tph_present;
                CQ_TPH_TYPE    <= cq_axi_user_tph_type;
                CQ_TPH_ST_TAG  <= cq_axi_user_tph_st_tag;
            end if;
            if (CQ_AXI_LAST = '1') then

                for i in 0 to ((AXI_DATA_WIDTH/32)/2-1) loop
                    if ((CQ_AXI_KEEP(i) = '1' and not (CQ_AXI_KEEP(i+1) = '0')) or (CQ_AXI_KEEP(i) = '1' and unsigned(CQ_AXI_KEEP) = 1)) then
                        eof(0) := '1';
                    end if;
                    if (CQ_AXI_KEEP(i+1) = '1' and i = ((AXI_DATA_WIDTH/32)/2-1)) then
                        eof(0) := '0';
                        eof(1) := '1';
                    end if;
                    exit when (CQ_AXI_KEEP(i) = '0');
                    eof_pos := eof_pos + 1;
                end loop;

                CQ_MFB_EOF_POS(EOP_POS_WIDTH-1 downto 0) <= std_logic_vector((eof_pos-1));
                eof_pos                                  := (others => '0');

                -- Check keep in second region
                for i in (AXI_DATA_WIDTH/32)/2 to ((AXI_DATA_WIDTH/32)-1) loop
                    exit when (CQ_AXI_KEEP(i) = '0');
                    eof_pos := eof_pos + 1;
                end loop;

                CQ_MFB_EOF_POS(2*EOP_POS_WIDTH-1 downto EOP_POS_WIDTH) <= std_logic_vector((eof_pos-1));
                CQ_MFB_EOF                                             <= eof;
            end if;
        end process;
    end generate;

    -- =========================================================================
    -- Parse FBE and LBE
    --
    -- It's defined for STRADDLING and non STRADDLING operation
    -- =========================================================================

    axi_straddling_g: if MFB_REGIONS = 2 generate
        fbe_lbe_str_pr : process (all)
        begin
            CQ_FBE <= (others => '0');
            CQ_LBE <= (others => '0');

            if (cq_axi_user_sop = "11") then
                CQ_FBE <= CQ_AXI_USER(8-1 downto 0);
                CQ_LBE <= CQ_AXI_USER(16-1 downto 8);
            elsif (cq_axi_user_sop = "01") then
                if (cq_axi_user_sop_ptr(0) = "10") then
                    CQ_FBE <= CQ_AXI_USER(4-1 downto 0) & "0000";
                    CQ_LBE <= CQ_AXI_USER(12-1 downto 8) & "0000";
                else
                    CQ_FBE <= "0000" & CQ_AXI_USER(4-1 downto 0);
                    CQ_LBE <= "0000" & CQ_AXI_USER(12-1 downto 8);
                end if;
            end if;
        end process;
    else generate
        CQ_FBE <= cq_axi_user_fbe when cq_axi_user_sop(0) = '1' else (others => '0');
        CQ_LBE <= cq_axi_user_lbe when cq_axi_user_sop(0) = '1' else (others => '0');
    end generate;

    CQ_MFB_DATA    <= CQ_AXI_DATA;
    CQ_MFB_SRC_RDY <= CQ_AXI_VALID;
    CQ_AXI_READY   <= CQ_MFB_DST_RDY;

end architecture;
