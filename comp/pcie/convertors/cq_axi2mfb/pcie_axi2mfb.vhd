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
-- Supported are 1024b, 512b and 256b with and without straddling, but
-- the 256b variants have not been tested.
entity PCIE_CQ_AXI2MFB is
    generic (
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        --
        -- Supported configurations are: (4,1,8,32), (2,1,8,32), (1,1,8,32)
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
        -- CQ_USER_WIDTH = 465 for Gen4x16 and Gen5x8 PCIe - with straddling and without straddling!
        -- CQ_USER_WIDTH = 231 for Gen3x16 PCIe            - with straddling and without straddling!
        -- CQ_USER_WIDTH = 183 for Gen3x16 PCIe            - with straddling and without straddling!
        -- CQ_USER_WIDTH = 88  for Gen3x8 PCIe             - without straddling!
        -- CQ_USER_WIDTH = 85  for Gen3x8 PCIe             - without straddling!
        -- =======================================================================

        AXI_CQUSER_WIDTH  : natural := 183;
        AXI_DATA_WIDTH    : natural := MFB_REGIONS*MFB_REGION_WIDTH;
        -- Straddling is permitted only for CQ_USER_WIDTH = 183, 231 or 465
        STRADDLING        : boolean := false;
        -- Select correct FPGA device: "VERSAL", "ULTRASCALE", "VIRTEX7"
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
    -- Number of is_sop_ptr encodings per MFB region
    constant SOP_PTR_DIV       : natural := max(1, 4/MFB_REGIONS);
    constant VERSAL_STRADDLING : boolean := STRADDLING and
                                            (AXI_CQUSER_WIDTH = 231 or AXI_CQUSER_WIDTH = 465);

    -- ========================================================================
    -- Functions
    -- ========================================================================

    function sop_ptr_region (ptr : std_logic_vector(2-1 downto 0)) return natural is
    begin
        return to_integer(unsigned(ptr)) / SOP_PTR_DIV;
    end function;

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
    signal cq_axi_user_sop_ptr     : slv_array_t(MFB_REGIONS-1 downto 0)(2-1 downto 0) := (others => (others => '0'));
    signal cq_axi_user_eop         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_axi_user_eop_ptr     : slv_array_t(MFB_REGIONS-1 downto 0)(5-1 downto 0);
    signal cq_axi_user_tph_present : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cq_axi_user_tph_type    : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal cq_axi_user_tph_st_tag  : std_logic_vector(MFB_REGIONS*8-1 downto 0);
    signal cq_axi_user_fbe         : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    signal cq_axi_user_lbe         : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    ---------------------------------------------------------------------------

begin
    assert ((MFB_REGIONS = 1 and (AXI_CQUSER_WIDTH = 85 or AXI_CQUSER_WIDTH = 88) and not STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 183 and STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 183 and not STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 231 and STRADDLING)
            or (MFB_REGIONS = 2 and AXI_CQUSER_WIDTH = 231 and not STRADDLING)
            or (MFB_REGIONS = 4 and AXI_CQUSER_WIDTH = 465 and STRADDLING)
            or (MFB_REGIONS = 4 and AXI_CQUSER_WIDTH = 465 and not STRADDLING))
        report "PCIE_CQ_AXI2MFB: Unsupported AXI CQ USER port width, the supported are: " &
               "85 (MFB_REGIONS = 1), 88 (MFB_REGIONS = 1), 183 (MFB_REGIONS = 2), " &
               "231 (MFB_REGIONS = 2), 465 (MFB_REGIONS = 4)"
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
        begin
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');

            if (cq_axi_user_sop(0) = '1') then
                CQ_TPH_PRESENT(0) <= CQ_AXI_USER(42);
                CQ_TPH_TYPE       <= CQ_AXI_USER(44 downto 43);
                CQ_TPH_ST_TAG     <= CQ_AXI_USER(52 downto 45);
            end if;
        end process;

        CQ_MFB_SOF     <= cq_axi_user_sop;
        CQ_MFB_SOF_POS <= (others => '0');
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for ULTRASCALE 512b variant with straddling
    -- =========================================================================

    axi_usp_512b_g: if (AXI_CQUSER_WIDTH = 183 and STRADDLING) generate
        cq_axi_user_sop         <=       CQ_AXI_USER(81 downto 80);
        cq_axi_user_sop_ptr(0)  <=       CQ_AXI_USER(83 downto 82);
        cq_axi_user_sop_ptr(1)  <=       CQ_AXI_USER(85 downto 84);
        cq_axi_user_eop         <=       CQ_AXI_USER(87 downto 86);
        cq_axi_user_eop_ptr(0)  <= '0' & CQ_AXI_USER(91 downto 88);
        cq_axi_user_eop_ptr(1)  <= '0' & CQ_AXI_USER(95 downto 92);

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
    -- Conversion AXI to MFB for VERSAL 512b and 1024b variants with straddling
    --
    -- See PG346, Completer Request Interface, tables of the CQ tuser signals.
    -- The is_sopN_ptr selects a byte lane of the start (512b: 00 = lane 0,
    -- 10 = lane 32; 1024b: 00, 01, 10, 11 = lane 0, 32, 64, 96), i.e. a 256b
    -- MFB region. The is_eopN_ptr is the offset of the last dword of the TLP.
    -- =========================================================================

    axi_versal_straddling_g: if VERSAL_STRADDLING generate
        constant IS_1024B      : boolean := (AXI_CQUSER_WIDTH = 465);
        constant SOP_LSB       : natural := tsel(IS_1024B, 160, 80);
        constant SOP_PTR_LSB   : natural := SOP_LSB + MFB_REGIONS;
        constant EOP_LSB       : natural := tsel(IS_1024B, 172, 86);
        constant EOP_PTR_LSB   : natural := EOP_LSB + MFB_REGIONS;
        constant EOP_PTR_WIDTH : natural := tsel(IS_1024B, 5, 4);
        constant EP_PAD        : std_logic_vector(5-EOP_PTR_WIDTH-1 downto 0) := (others => '0');
    begin
        cq_axi_user_sop <= CQ_AXI_USER(SOP_LSB+MFB_REGIONS-1 downto SOP_LSB);
        cq_axi_user_eop <= CQ_AXI_USER(EOP_LSB+MFB_REGIONS-1 downto EOP_LSB);

        user_ptr_g : for i in 0 to MFB_REGIONS-1 generate
            constant SP_LSB : natural := SOP_PTR_LSB + i*2;
            constant EP_LSB : natural := EOP_PTR_LSB + i*EOP_PTR_WIDTH;
        begin
            cq_axi_user_sop_ptr(i) <= CQ_AXI_USER(SP_LSB+2-1 downto SP_LSB);
            cq_axi_user_eop_ptr(i) <= EP_PAD & CQ_AXI_USER(EP_LSB+EOP_PTR_WIDTH-1 downto EP_LSB);
        end generate;

        sop_eop_sof_eof_conv_pr : process (all)
            variable region  : natural range 0 to MFB_REGIONS-1;
            variable eof_pos : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_POS_WIDTH-1 downto 0);
        begin
            CQ_MFB_SOF     <= (others => '0');
            CQ_MFB_EOF     <= (others => '0');
            CQ_MFB_SOF_POS <= (others => '0');
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');
            eof_pos        := (others => (others => '0'));

            for i in 0 to MFB_REGIONS-1 loop
                if (cq_axi_user_sop(i) = '1') then
                    region             := sop_ptr_region(cq_axi_user_sop_ptr(i));
                    CQ_MFB_SOF(region) <= '1';
                end if;

                if (cq_axi_user_eop(i) = '1') then
                    region             := to_integer(unsigned(cq_axi_user_eop_ptr(i))) / 8;
                    CQ_MFB_EOF(region) <= '1';
                    eof_pos(region)    := cq_axi_user_eop_ptr(i)(EOP_POS_WIDTH-1 downto 0);
                end if;
            end loop;

            CQ_MFB_EOF_POS <= slv_array_ser(eof_pos);
        end process;
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for ULTRASCALE 512b variant
    -- =========================================================================

    axi_usp_512b_no_straddling_g: if (AXI_CQUSER_WIDTH = 183 and not STRADDLING) generate
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
        begin
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');

            if (CQ_AXI_USER(80) = '1') then
                CQ_TPH_PRESENT <= cq_axi_user_tph_present;
                CQ_TPH_TYPE    <= cq_axi_user_tph_type;
                CQ_TPH_ST_TAG  <= cq_axi_user_tph_st_tag;
            end if;
        end process;
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for VERSAL 512b variant
    -- =========================================================================

    axi_versal_512b_no_straddling_g: if (AXI_CQUSER_WIDTH = 231 and not STRADDLING) generate
        cq_axi_user_sop(0)      <= CQ_AXI_USER(80);
        cq_axi_user_sop(1)      <= '0';
        CQ_MFB_SOF              <= cq_axi_user_sop;
        CQ_MFB_SOF_POS          <= (others => '0');
        cq_axi_user_fbe         <= "0000" & CQ_AXI_USER(4-1 downto 0);
        cq_axi_user_lbe         <= "0000" & CQ_AXI_USER(12-1 downto 8);
        CQ_TPH_PRESENT          <= (others => '0');
        CQ_TPH_TYPE             <= (others => '0');
        CQ_TPH_ST_TAG           <= (others => '0');
    end generate;

    -- =========================================================================
    -- Conversion AXI to MFB for VERSAL 1024b variant
    -- =========================================================================

    axi_1024b_no_straddling_g: if (AXI_CQUSER_WIDTH = 465 and not STRADDLING) generate
        cq_axi_user_sop(0)      <= CQ_AXI_USER(160);
        cq_axi_user_sop(1)      <= '0';
        cq_axi_user_sop(2)      <= '0';
        cq_axi_user_sop(3)      <= '0';
        CQ_MFB_SOF_POS          <= (others => '0');
        cq_axi_user_fbe         <= "0000" & "0000" & "0000" & CQ_AXI_USER(132-1 downto 128);
        cq_axi_user_lbe         <= "0000" & "0000" & "0000" & CQ_AXI_USER(148-1 downto 144);

        cq_axi_user_sop_ptr(0)  <= CQ_AXI_USER(166 -  1 downto 164);

        conv_pr : process (all)
            variable ptr_sop : integer := 0;
        begin
            CQ_TPH_PRESENT <= (others => '0');
            CQ_TPH_TYPE    <= (others => '0');
            CQ_TPH_ST_TAG  <= (others => '0');
            CQ_MFB_SOF     <= (others => '0');

            case cq_axi_user_sop_ptr(0) is
                when "00"   => ptr_sop := 0;
                when "01"   => ptr_sop := 1;
                when "10"   => ptr_sop := 2;
                when "11"   => ptr_sop := 3;
                when others => ptr_sop := 0;
            end case;

            if (cq_axi_user_sop(0) = '1') then
                CQ_MFB_SOF(ptr_sop) <= '1';
            end if;
        end process;
    end generate;

    -- =========================================================================
    -- EOF and EOF_POS of all variants without straddling
    --
    -- The frame ends in the last region with a valid dword.
    -- =========================================================================

    no_straddling_eof_g : if not STRADDLING generate
        constant REGION_DWORDS : natural := AXI_DATA_WIDTH/32/MFB_REGIONS;
    begin
        assert ((AXI_DATA_WIDTH/32) mod MFB_REGIONS = 0)
            report "PCIE_CQ_AXI2MFB: AXI_DATA_WIDTH/32 must be divisible by MFB_REGIONS!"
            severity failure;

        eof_pr : process (all)
            -- The extra invalid dword ends the frame in the last region.
            variable keep    : std_logic_vector(AXI_DATA_WIDTH/32 downto 0);
            variable eof_pos : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_POS_WIDTH-1 downto 0);
        begin
            keep    := '0' & CQ_AXI_KEEP;
            eof_pos := (others => (others => '0'));

            CQ_MFB_EOF <= (others => '0');

            if (CQ_AXI_LAST = '1') then
                for r in 0 to MFB_REGIONS-1 loop
                    CQ_MFB_EOF(r) <= keep(r*REGION_DWORDS) and not keep((r+1)*REGION_DWORDS);
                    for i in 0 to REGION_DWORDS-1 loop
                        if (keep(r*REGION_DWORDS+i) = '1') then
                            eof_pos(r) := std_logic_vector(to_unsigned(i, EOP_POS_WIDTH));
                        end if;
                    end loop;
                end loop;
            end if;

            CQ_MFB_EOF_POS <= slv_array_ser(eof_pos);
        end process;
    end generate;

    -- =========================================================================
    -- Parse FBE and LBE
    --
    -- It's defined for STRADDLING and non STRADDLING operation
    -- =========================================================================

    axi_straddling_g: if MFB_REGIONS > 1 generate
        constant FBE_LSB : natural := tsel(AXI_CQUSER_WIDTH = 465, 128, 0);
        constant LBE_LSB : natural := FBE_LSB + MFB_REGIONS*4;
    begin
        -- The first_be and last_be fields belong to the N-th TLP starting in the word.
        fbe_lbe_str_pr : process (all)
            variable region : natural range 0 to MFB_REGIONS-1;
            variable fbe    : natural;
            variable lbe    : natural;
        begin
            CQ_FBE <= (others => '0');
            CQ_LBE <= (others => '0');

            for i in 0 to MFB_REGIONS-1 loop
                if (cq_axi_user_sop(i) = '1') then
                    region                             := sop_ptr_region(cq_axi_user_sop_ptr(i));
                    fbe                                := FBE_LSB + i*4;
                    lbe                                := LBE_LSB + i*4;
                    CQ_FBE(region*4+3 downto region*4) <= CQ_AXI_USER(fbe+3 downto fbe);
                    CQ_LBE(region*4+3 downto region*4) <= CQ_AXI_USER(lbe+3 downto lbe);
                end if;
            end loop;
        end process;
    else generate
        CQ_FBE <= cq_axi_user_fbe when cq_axi_user_sop(0) = '1' else (others => '0');
        CQ_LBE <= cq_axi_user_lbe when cq_axi_user_sop(0) = '1' else (others => '0');
    end generate;

    CQ_MFB_DATA    <= CQ_AXI_DATA;
    CQ_MFB_SRC_RDY <= CQ_AXI_VALID;
    CQ_AXI_READY   <= CQ_MFB_DST_RDY;

end architecture;
