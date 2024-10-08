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
   generic(
      -- =======================================================================
      -- MFB BUS CONFIGURATION:
      -- =======================================================================
      -- Supported configurations are: (2,1,8,32), (1,1,8,32)
      MFB_REGIONS      : natural := 2;
      MFB_REGION_SIZE  : natural := 1;
      MFB_BLOCK_SIZE   : natural := 8;
      MFB_ITEM_WIDTH   : natural := 32;
      -- =======================================================================
      -- AXI BUS CONFIGURATION:
      -- =======================================================================
      -- RQ_USER_WIDTH = 137 for Gen3x16 PCIe - with straddling!
      -- RQ_USER_WIDTH = 62  for Gen3x8 PCIe - without straddling!
      -- RQ_USER_WIDTH = 60  for Gen3x8 PCIe - without straddling!
      AXI_RQUSER_WIDTH : natural := 137
      );
   port(
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

   constant EOF_POS_WIDTH : natural := log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE);

   signal s_rx_mfb_eof_pos_arr : slv_array_t(MFB_REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
   signal s_rx_mfb_be_arr      : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);

   signal s_rq_last : std_logic;
   signal s_rq_keep : std_logic_vector(RQ_DATA'length/32-1 downto 0);

   signal s_is_sop      : std_logic_vector(1 downto 0);
   signal s_is_sop0_ptr : std_logic_vector(1 downto 0);
   signal s_is_sop1_ptr : std_logic_vector(1 downto 0);

   signal s_is_eop      : std_logic_vector(1 downto 0);
   signal s_is_eop0_ptr : std_logic_vector(3 downto 0);
   signal s_is_eop1_ptr : std_logic_vector(3 downto 0);

   signal s_first_be0 : std_logic_vector(3 downto 0);
   signal s_last_be0  : std_logic_vector(3 downto 0);

   signal s_first_be1 : std_logic_vector(3 downto 0);
   signal s_last_be1  : std_logic_vector(3 downto 0);

   signal s_first_be : std_logic_vector(7 downto 0);
   signal s_last_be  : std_logic_vector(7 downto 0);

   signal s_rq_user : std_logic_vector(AXI_RQUSER_WIDTH-1 downto 0);

begin

   assert ((MFB_REGIONS = 1 or MFB_REGIONS = 2) and MFB_REGION_SIZE = 1 and MFB_BLOCK_SIZE = 8 and MFB_ITEM_WIDTH = 32)
      report "PTC_MFB2PCIE_AXI: Unsupported MFB configuration, the allowed are: (2,1,8,32), (1,1,8,32)"
      severity FAILURE;

   assert (AXI_RQUSER_WIDTH = 60 or AXI_RQUSER_WIDTH = 62 or AXI_RQUSER_WIDTH = 137)
      report "PTC_MFB2PCIE_AXI: Unsupported AXI RQ USER port width, the supported are: 60, 62, 137"
      severity FAILURE;

   -- --------------------------------------------------------------------------
   --  PREPARE AXI SIGNALS
   -- --------------------------------------------------------------------------

   -- is high when is word with end of packet, in straddle mode is not useful
   s_rq_last <= or RX_MFB_EOF;

   two_region_tuser_gen : if (MFB_REGIONS = 2) generate
      -- create array of end of frame position
      s_rx_mfb_eof_pos_arr <= slv_array_downto_deser(RX_MFB_EOF_POS, MFB_REGIONS, EOF_POS_WIDTH);

      -- create array of byte enables
      s_rx_mfb_be_arr <= slv_array_downto_deser(RX_MFB_BE, MFB_REGIONS, 8);

      -- keep in straddle mode is not useful therefore, all bits are set to VCC
      s_rq_keep <= (others => '1');

      -- create SOP flags and pointers for AXI
      s_is_sop(0)   <= or RX_MFB_SOF;
      s_is_sop(1)   <= and RX_MFB_SOF;
      s_is_sop0_ptr <= "10" when (RX_MFB_SOF = "10") else "00";
      s_is_sop1_ptr <= "10";

      -- create EOP flags and pointers for AXI
      s_is_eop(0)   <= or RX_MFB_EOF;
      s_is_eop(1)   <= and RX_MFB_EOF;
      s_is_eop0_ptr <= '1' & s_rx_mfb_eof_pos_arr(1) when (RX_MFB_EOF = "10") else '0' & s_rx_mfb_eof_pos_arr(0);
      s_is_eop1_ptr <= '1' & s_rx_mfb_eof_pos_arr(1);

      -- set byte enables for first packet in word
      s_first_be0 <= s_rx_mfb_be_arr(0)(3 downto 0) when RX_MFB_SOF(0) = '1' else s_rx_mfb_be_arr(1)(3 downto 0);
      s_last_be0  <= s_rx_mfb_be_arr(0)(7 downto 4) when RX_MFB_SOF(0) = '1' else s_rx_mfb_be_arr(1)(7 downto 4);

      -- set byte enables for second packet in word
      s_first_be1 <= s_rx_mfb_be_arr(1)(3 downto 0);
      s_last_be1  <= s_rx_mfb_be_arr(1)(7 downto 4);

      -- prepare byte enables for request interface
      s_first_be <= s_first_be1 & s_first_be0;
      s_last_be  <= s_last_be1 & s_last_be0;

      -- create request user signal
      s_rq_user <= (AXI_RQUSER_WIDTH-1 downto 36 => '0') & s_is_eop1_ptr & s_is_eop0_ptr & s_is_eop &
                   s_is_sop1_ptr & s_is_sop0_ptr & s_is_sop & "0000" & s_last_be & s_first_be;
   end generate;

   one_region_tuser_gen : if (MFB_REGIONS = 1) generate
      -- keep signal serves as valid for each DWORD of RQ_DATA signal
      s_rq_keep_pr : process (all)
      begin
         if (RX_MFB_SRC_RDY = '0') then  -- no data

            s_rq_keep <= (others => '0');

         elsif (RX_MFB_EOF(0) = '1') then  -- end of data

            s_rq_keep <= (others => '0');

            for i in 0 to RQ_DATA'length/32-1 loop
               s_rq_keep(i) <= '1';
               exit when (i = to_integer(unsigned(RX_MFB_EOF_POS)));
            end loop;

         else                           -- start or middle of data

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
