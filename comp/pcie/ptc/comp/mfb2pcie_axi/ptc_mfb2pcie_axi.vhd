-- ptc_mfb2pcie_axi.vhd: MFB to PCIE AXI convertor
-- Copyright (C) 2018 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Vladislav Valek <valekv@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity PTC_MFB2PCIE_AXI is
    generic (
        -- =======================================================================
        -- MFB BUS CONFIGURATION:
        -- =======================================================================
        -- Supported configurations are: (4,1,8,32), (2,1,8,32), (1,1,8,32)
        MFB_REGIONS      : natural := 2;
        MFB_REGION_SIZE  : natural := 1;
        MFB_BLOCK_SIZE   : natural := 8;
        MFB_ITEM_WIDTH   : natural := 32;
        -- =======================================================================
        -- AXI BUS CONFIGURATION:
        -- =======================================================================
        -- RQ_USER_WIDTH = 373 for Gen4x16 PCIe - with straddling!
        -- RQ_USER_WIDTH = 183 for Gen3x16 PCIe - with straddling!
        -- RQ_USER_WIDTH = 137 for Gen3x16 PCIe - with straddling!
        -- RQ_USER_WIDTH = 62  for Gen3x8 PCIe - without straddling!
        -- RQ_USER_WIDTH = 60  for Gen3x8 PCIe - without straddling!
        AXI_RQUSER_WIDTH : natural := 137
    );
    port (
        -- =======================================================================
        -- INPUT MFB INTERFACE
        -- =======================================================================
        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE)) -1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE)) -1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS -1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;
        -- PCIe transaction length last and first DWORD byte enable (MSB -> last byte, LSB -> first byte)
        RX_MFB_BE      : in  std_logic_vector(MFB_REGIONS*8 -1 downto 0);
        --============================================================================================

        -- =======================================================================
        -- OUTPUT AXI REQUESTER REQUEST INTERFACE (RQ)
        -- =======================================================================
        -- Data bus
        RQ_DATA  : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH -1 downto 0);
        -- Set of signals with sideband information about transferred transaction
        RQ_USER  : out std_logic_vector(AXI_RQUSER_WIDTH -1 downto 0);
        -- Indication of the last word of a transaction
        RQ_LAST  : out std_logic;
        -- Indication of valid data
        -- each bit determines validity of different Dword (1 Dword = 4 Bytes)
        RQ_KEEP  : out std_logic_vector((MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH)/32 -1 downto 0);
        -- PCIe core is ready to receive a transaction
        RQ_READY : in  std_logic;
        -- User application sends valid data
        RQ_VALID : out std_logic
    --============================================================================================
    );
end entity;

architecture FULL of PTC_MFB2PCIE_AXI is

    constant EOF_POS_WIDTH  : natural := log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE);
    -- is_sop_ptr has four positions in a word, the start of region r is position r*4/MFB_REGIONS
    constant SOP_PTR_STEP   : natural := 4/MFB_REGIONS;
    -- is_eop_ptr is the last dword of the packet in the word
    constant EOP_PTR_WIDTH  : natural := log2(MFB_REGIONS) + EOF_POS_WIDTH;
    -- addr_offset field between the byte enables and is_sop, unused
    constant ADDR_OFS_WIDTH : natural := tsel(MFB_REGIONS = 4, 16, 4);
    -- byte enables, addr_offset, is_sop, is_sop_ptr, is_eop, is_eop_ptr
    constant RQ_USER_USED   : natural := MFB_REGIONS*8 + ADDR_OFS_WIDTH + MFB_REGIONS*(1+2+1+EOP_PTR_WIDTH);

    signal s_rx_mfb_eof_pos_arr : slv_array_t(MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal s_rx_mfb_be_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);

    signal s_rq_last : std_logic;
    signal s_rq_keep : std_logic_vector(RQ_DATA'length/32-1 downto 0);

    -- SOP and EOP slots of the k-th packet starting and ending in the word
    signal s_is_sop     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_is_sop_ptr : slv_array_t(MFB_REGIONS-1 downto 0)(2-1 downto 0);
    signal s_is_eop     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s_is_eop_ptr : slv_array_t(MFB_REGIONS-1 downto 0)(EOP_PTR_WIDTH-1 downto 0);

    signal s_first_be : std_logic_vector(MFB_REGIONS*4-1 downto 0);
    signal s_last_be  : std_logic_vector(MFB_REGIONS*4-1 downto 0);

    signal s_rq_user : std_logic_vector(AXI_RQUSER_WIDTH-1 downto 0);

begin

    assert ((MFB_REGIONS = 1 or MFB_REGIONS = 2 or MFB_REGIONS = 4) and MFB_REGION_SIZE = 1 and MFB_BLOCK_SIZE = 8 and MFB_ITEM_WIDTH = 32)
        report "PTC_MFB2PCIE_AXI: Unsupported MFB configuration, the allowed are: (4,1,8,32), (2,1,8,32), (1,1,8,32)"
        severity FAILURE;

    assert ((MFB_REGIONS = 1 and (AXI_RQUSER_WIDTH = 60 or AXI_RQUSER_WIDTH = 62))
            or (MFB_REGIONS = 2 and (AXI_RQUSER_WIDTH = 137 or AXI_RQUSER_WIDTH = 183))
            or (MFB_REGIONS = 4 and AXI_RQUSER_WIDTH = 373))
        report "PTC_MFB2PCIE_AXI: Unsupported combination of MFB_REGIONS and AXI_RQUSER_WIDTH, "
               & "the supported are: 1 and 60 or 62, 2 and 137 or 183, 4 and 373"
        severity FAILURE;

    -- --------------------------------------------------------------------------
    --  PREPARE AXI SIGNALS
    -- --------------------------------------------------------------------------

    -- is high when is word with end of packet, in straddle mode is not useful
    s_rq_last <= or RX_MFB_EOF;

    straddling_tuser_gen : if (MFB_REGIONS > 1) generate
        s_rx_mfb_eof_pos_arr <= slv_array_deser(RX_MFB_EOF_POS, MFB_REGIONS);
        s_rx_mfb_be_arr      <= slv_array_deser(RX_MFB_BE, MFB_REGIONS);

        -- keep in straddle mode is not useful therefore, all bits are set to VCC
        s_rq_keep <= (others => '1');

        -- The k-th packet starting (ending) in the word takes the k-th SOP (EOP) slot (PG213, PG346).
        s_sop_eop_pr : process (all)
            variable sop_slot : natural range 0 to MFB_REGIONS;
            variable eop_slot : natural range 0 to MFB_REGIONS;
        begin
            s_is_sop     <= (others => '0');
            s_is_sop_ptr <= (others => (others => '0'));
            s_is_eop     <= (others => '0');
            s_is_eop_ptr <= (others => (others => '0'));
            s_first_be   <= (others => '0');
            s_last_be    <= (others => '0');
            sop_slot     := 0;
            eop_slot     := 0;

            for r in 0 to MFB_REGIONS-1 loop
                if (RX_MFB_SOF(r) = '1') then
                    s_is_sop(sop_slot)     <= '1';
                    s_is_sop_ptr(sop_slot) <= std_logic_vector(to_unsigned(r*SOP_PTR_STEP, 2));

                    s_first_be(sop_slot*4+3 downto sop_slot*4) <= s_rx_mfb_be_arr(r)(3 downto 0);
                    s_last_be(sop_slot*4+3 downto sop_slot*4)  <= s_rx_mfb_be_arr(r)(7 downto 4);

                    sop_slot := sop_slot + 1;
                end if;

                if (RX_MFB_EOF(r) = '1') then
                    s_is_eop(eop_slot)     <= '1';
                    s_is_eop_ptr(eop_slot) <= std_logic_vector(to_unsigned(r, log2(MFB_REGIONS)))
                                              & s_rx_mfb_eof_pos_arr(r);

                    eop_slot := eop_slot + 1;
                end if;
            end loop;
        end process;

        s_rq_user <= (AXI_RQUSER_WIDTH-1 downto RQ_USER_USED => '0')
                     & slv_array_ser(s_is_eop_ptr) & s_is_eop
                     & slv_array_ser(s_is_sop_ptr) & s_is_sop
                     & std_logic_vector(to_unsigned(0, ADDR_OFS_WIDTH))
                     & s_last_be & s_first_be;
    end generate;

    one_region_tuser_gen : if (MFB_REGIONS = 1) generate
        -- keep signal serves as valid for each DWORD of RQ_DATA signal
        s_rq_keep_pr : process (all)
        begin
            if (RX_MFB_SRC_RDY = '0') then                                -- no data

                s_rq_keep <= (others => '0');

            elsif (RX_MFB_EOF(0) = '1') then                              -- end of data

                s_rq_keep <= (others => '0');

                for i in 0 to RQ_DATA'length/32-1 loop
                    s_rq_keep(i) <= '1';
                    exit when (i = to_integer(unsigned(RX_MFB_EOF_POS)));
                end loop;

            else                                                          -- start or middle of data

                s_rq_keep <= (others => '1');

            end if;
        end process;

        -- create request user signal
        s_rq_user <= (AXI_RQUSER_WIDTH-1 downto 8 => '0') & RX_MFB_BE;
    end generate;

    -- --------------------------------------------------------------------------
    --  AXI SIGNALS ASSIGNMENT
    -- --------------------------------------------------------------------------

    RX_MFB_DST_RDY <= RQ_READY;

    RQ_DATA  <= RX_MFB_DATA;
    RQ_USER  <= s_rq_user;
    RQ_LAST  <= s_rq_last;
    RQ_KEEP  <= s_rq_keep;
    RQ_VALID <= RX_MFB_SRC_RDY;

end architecture;
