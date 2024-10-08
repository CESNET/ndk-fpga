-- ptc_dma2pcie_hdr_transform_full.vhd: DMA to PCIe header transform for PTC component - architecture
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for DMA MVB header fields

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture full of PTC_DMA2PCIE_HDR_TRANSFORM is

   ---------------------------------------------------------------------------
   -- Constants
   ---------------------------------------------------------------------------

   constant DMA_LEN_WIDTH : integer := DMA_REQUEST_LENGTH'high-DMA_REQUEST_LENGTH'low+1;

   ---------------------------------------------------------------------------

   ---------------------------------------------------------------------------
   -- Signals
   ---------------------------------------------------------------------------

   signal rx_mvb_data_reg     : std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
   signal rx_mvb_vld_reg      : std_logic_vector(MVB_ITEMS                -1 downto 0);
   signal rx_mvb_src_rdy_reg  : std_logic;

   -- TAGM MVB OUT converted to slv_array_t
   signal TAGM_MVB_OUT_arr : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_UPHDR_WIDTH-1 downto 0);

   -- selected fields from TAGM MVB OUT
   signal tagm_mvb_out_addr    : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_REQUEST_GLOBAL'high-DMA_REQUEST_GLOBAL'low downto 2);
   signal tagm_mvb_out_tag_all : slv_array_t(MVB_ITEMS-1 downto 0)(PCIE_TAG_WIDTH-1 downto 0);
   signal tagm_mvb_out_tag_low : slv_array_t(MVB_ITEMS-1 downto 0)(8-1 downto 0);
   signal tagm_mvb_out_tag_8   : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal tagm_mvb_out_tag_9   : std_logic_vector(MVB_ITEMS-1 downto 0);
   signal tagm_mvb_out_vfid    : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_REQUEST_VFID);
   signal tagm_mvb_out_len     : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_REQUEST_LENGTH);
   signal tagm_mvb_out_type    : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_REQUEST_TYPE);
   signal tagm_mvb_out_relaxed : slv_array_t(MVB_ITEMS-1 downto 0)(DMA_REQUEST_RELAXED);
   signal tagm_mvb_out_fbe     : slv_array_t(MVB_ITEMS-1 downto 0)(4-1 downto 0);
   signal tagm_mvb_out_lbe     : slv_array_t(MVB_ITEMS-1 downto 0)(4-1 downto 0);

    function decode_be(ib : std_logic_vector(1 downto 0); first : boolean) return std_logic_vector is
        variable be : std_logic_vector(3 downto 0);
        variable ret : std_logic_vector(3 downto 0);
    begin
        case ib is
            when "00" => be := "1111";
            when "01" => be := "0111";
            when "10" => be := "0011";
            when "11" => be := "0001";
            when others => be := "1111";
        end case;

        for i in 0 to 4-1 loop
            ret(i) := be(3-i) when first else be(i);
        end loop;

        return ret;
    end function;

   ---------------------------------------------------------------------------

begin

   assert (DEVICE = "STRATIX10" OR DEVICE = "AGILEX" OR DEVICE = "ULTRASCALE" OR DEVICE = "7SERIES")
      report "PTC_DMA2PCIE_HDR_TRANSFORM: unsupported device!" severity failure;

   -- -------------------------------------------------------------------------
   -- Inserting RX MVB in Tag manager
   -- -------------------------------------------------------------------------

   -- register between MVB ASFIFO and Tag Manager
   tagm_mvb_in_reg : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_MVB_DST_RDY='1') then
            rx_mvb_data_reg    <= RX_MVB_DATA;
            rx_mvb_vld_reg     <= RX_MVB_VLD;
            rx_mvb_src_rdy_reg <= RX_MVB_SRC_RDY;
         end if;

         if (RESET='1') then
            rx_mvb_src_rdy_reg <= '0';
         end if;
      end if;
   end process;

   tagm_mvb_in_reg2 : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         if (RX_MVB_DST_RDY='1') then
            TAGM_MVB_IN         <= rx_mvb_data_reg;
            TAGM_MVB_IN_VLD     <= rx_mvb_vld_reg;
            TAGM_MVB_IN_SRC_RDY <= rx_mvb_src_rdy_reg;
         end if;

         if (RESET='1') then
            TAGM_MVB_IN_SRC_RDY <= '0';
         end if;
      end if;
   end process;

   RX_MVB_DST_RDY <= TAGM_MVB_IN_DST_RDY;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- TAGM MVB OUT organizing
   -- -------------------------------------------------------------------------

   tagm_out_org_gen : for i in 0 to MVB_ITEMS-1 generate
      TAGM_MVB_OUT_arr(i)  <= TAGM_MVB_OUT(DMA_UPHDR_WIDTH*(i+1)-1 downto DMA_UPHDR_WIDTH*i);

      tagm_mvb_out_addr(i)    <= TAGM_MVB_OUT_arr(i)(DMA_REQUEST_GLOBAL'high downto DMA_REQUEST_GLOBAL'low+2);
      tagm_mvb_out_tag_all(i) <= TAGM_MVB_OUT_TAG(PCIE_TAG_WIDTH*(i+1)-1 downto PCIE_TAG_WIDTH*i);
      tagm_mvb_out_vfid(i)    <= TAGM_MVB_OUT_arr(i)(DMA_REQUEST_VFID);
      tagm_mvb_out_len(i)     <= TAGM_MVB_OUT_arr(i)(DMA_REQUEST_LENGTH);
      tagm_mvb_out_type(i)    <= TAGM_MVB_OUT_arr(i)(DMA_REQUEST_TYPE);
      tagm_mvb_out_relaxed(i) <= TAGM_MVB_OUT_arr(i)(DMA_REQUEST_RELAXED);
      tagm_mvb_out_fbe(i)     <= decode_be(TAGM_MVB_OUT_arr(i)(DMA_REQUEST_FIRSTIB), true);
      tagm_mvb_out_lbe(i)     <= decode_be(TAGM_MVB_OUT_arr(i)(DMA_REQUEST_LASTIB), false);
   end generate;

   -- Separate PCIe Tag to 1,1,8 bits
   tag_separate_pr : process (tagm_mvb_out_tag_all)
      variable tag_tmp : std_logic_vector(8*PCIE_TAG_WIDTH-1 downto 0);
   begin
      for i in 0 to MVB_ITEMS-1 loop
         tag_tmp := std_logic_vector(resize_left(unsigned(tagm_mvb_out_tag_all(i)),tag_tmp'length));
         tagm_mvb_out_tag_low(i) <= tag_tmp(8-1 downto 0);
         tagm_mvb_out_tag_8  (i) <= tag_tmp(8);
         tagm_mvb_out_tag_9  (i) <= tag_tmp(9);
      end loop;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- TX Byte enable and Payload generation
   -- -------------------------------------------------------------------------

   tx_be_gen : for i in 0 to MVB_ITEMS-1 generate
      TX_MVB_BE(8*(i+1)-1 downto 8*i) <= X"00" when to_integer(unsigned(tagm_mvb_out_len(i)))=0 else
                                         X"0" & (tagm_mvb_out_fbe(i) and tagm_mvb_out_lbe(i)) when to_integer(unsigned(tagm_mvb_out_len(i)))=1 else
                                         tagm_mvb_out_lbe(i) & tagm_mvb_out_fbe(i);
   end generate;

   tx_payload_gen : for i in 0 to MVB_ITEMS-1 generate
      TX_MVB_PAYLOAD(i) <= '1' when TAGM_MVB_OUT_arr(i)(DMA_REQUEST_TYPE)=DMA_TYPE_WRITE else '0';
   end generate;

   tx_payload_size_gen : for i in 0 to MVB_ITEMS-1 generate
      TX_MVB_PAYLOAD_SIZE(TRANS_SIZE_WIDTH*(i+1)-1 downto TRANS_SIZE_WIDTH*i) <= tagm_mvb_out_len(i)(TRANS_SIZE_WIDTH-1 downto 0);
   end generate;

   tx_header_type_intel_gen : if (DEVICE="STRATIX10" or DEVICE="AGILEX") generate
      tx_header_type_gen : for i in 0 to MVB_ITEMS-1 generate
         TX_MVB_TYPE(i) <= '0' when tagm_mvb_out_addr(i)(64-1 downto 32)=(64-1 downto 32 => '0') else '1';
      end generate;
   end generate;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- TX PCIe MVB composing
   -- -------------------------------------------------------------------------
   tx_mvb_gen : for i in 0 to MVB_ITEMS-1 generate
      pcie_rq_hdr_gen_i : entity work.PCIE_RQ_HDR_GEN
      generic map(
         DEVICE       => DEVICE
      )
      port map(
         IN_ADDRESS    => tagm_mvb_out_addr(i),
         IN_VFID       => tagm_mvb_out_vfid(i),
         IN_TAG        => tagm_mvb_out_tag_9(i) & tagm_mvb_out_tag_8(i) & tagm_mvb_out_tag_low(i),
         IN_FBE        => TX_MVB_BE(i*8+4-1 downto i*8+0),
         IN_LBE        => TX_MVB_BE(i*8+8-1 downto i*8+4),
         IN_REQ_TYPE   => tagm_mvb_out_type(i)(DMA_REQUEST_TYPE_O),
         IN_ADDR_LEN   => TX_MVB_TYPE(i),
         IN_ATTRIBUTES => '0' & tagm_mvb_out_relaxed(i) & '0',
         IN_DW_CNT     => tagm_mvb_out_len(i),
         OUT_HEADER    => TX_MVB_DATA(PCIE_UPHDR_WIDTH*(i+1)-1 downto PCIE_UPHDR_WIDTH*i)
      );
   end generate;

   TX_MVB_VLD           <= TAGM_MVB_OUT_VLD;
   TX_MVB_SRC_RDY       <= TAGM_MVB_OUT_SRC_RDY;
   TAGM_MVB_OUT_DST_RDY <= TX_MVB_DST_RDY;

   -- -------------------------------------------------------------------------

end architecture;
