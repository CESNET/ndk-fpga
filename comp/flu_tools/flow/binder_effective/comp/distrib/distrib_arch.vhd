--
-- distrib_arch.vhd: FLU Frame RR distributor
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of DISTRIB is
   --! FLU input signals
   signal in_rx_data       : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos    : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop        : std_logic;
   signal in_rx_eop        : std_logic;
   signal in_rx_src_rdy    : std_logic;
   signal in_rx_dst_rdy    : std_logic;

   --! Signal for distribute information
   signal distributed_to_out : std_logic;

   --! FLU output signals - lane 0
   signal out_tx_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_tx_sop_pos0   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal out_tx_eop_pos0   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal out_tx_sop0       : std_logic;
   signal out_tx_eop0       : std_logic;
   signal out_tx_src_rdy0   : std_logic;
   signal out_tx_dst_rdy0   : std_logic;

   --! FLU output signals - lane 0
   signal out_tx_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_tx_sop_pos1   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal out_tx_eop_pos1   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal out_tx_sop1       : std_logic;
   signal out_tx_eop1       : std_logic;
   signal out_tx_src_rdy1   : std_logic;
   signal out_tx_dst_rdy1   : std_logic;

   --! FLU distributor control
   signal flu_distrib_mask  : std_logic_vector(1 downto 0);
   signal flu_distrib_rdy   : std_logic;
   signal flu_distrib_next  : std_logic;

begin

   -- -------------------------------------------------------------------------
   -- Input port map
   -- -------------------------------------------------------------------------
   -- Deal with map of the input RX flow
   in_rx_data        <= RX_DATA;
   in_rx_sop_pos     <= RX_SOP_POS;
   in_rx_eop_pos     <= RX_EOP_POS;
   in_rx_sop         <= RX_SOP;
   in_rx_eop         <= RX_EOP;
   in_rx_src_rdy     <= RX_SRC_RDY;
   RX_DST_RDY        <= in_rx_dst_rdy;

   DISTRIBUTED_TO    <= distributed_to_out;


   FLU_DISTRIB_I:entity work.FLU_DISTRIBUTOR_1TO2
      generic map(
          DATA_WIDTH       => DATA_WIDTH,
          SOP_POS_WIDTH    => SOP_POS_WIDTH
      )
      port map(
          -- Common interface
         RESET          => RESET,
         CLK            => CLK,

         -- Frame Link Unaligned input interface
         RX_DATA        => in_rx_data,
         RX_SOP_POS     => in_rx_sop_pos,
         RX_EOP_POS     => in_rx_eop_pos,
         RX_SOP         => in_rx_sop,
         RX_EOP         => in_rx_eop,
         RX_SRC_RDY     => in_rx_src_rdy,
         RX_DST_RDY     => in_rx_dst_rdy,

         -- Frame Link Unaligned output interfaces
         -- Interface 0
         TX0_DATA       => out_tx_data0,
         TX0_SOP_POS    => out_tx_sop_pos0,
         TX0_EOP_POS    => out_tx_eop_pos0,
         TX0_SOP        => out_tx_sop0,
         TX0_EOP        => out_tx_eop0,
         TX0_SRC_RDY    => out_tx_src_rdy0,
         TX0_DST_RDY    => out_tx_dst_rdy0,

         -- Interface 1
         TX1_DATA       => out_tx_data1,
         TX1_SOP_POS    => out_tx_sop_pos1,
         TX1_EOP_POS    => out_tx_eop_pos1,
         TX1_SOP        => out_tx_sop1,
         TX1_EOP        => out_tx_eop1,
         TX1_SRC_RDY    => out_tx_src_rdy1,
         TX1_DST_RDY    => out_tx_dst_rdy1,

         -- Distribution control interface
         INUM_MASK      => flu_distrib_mask,
         INUM_READY     => flu_distrib_rdy,
         INUM_NEXT      => flu_distrib_next
        );

   --! Generation of distribution mask (select the fit active output)
   --flu_distrib_mask <=  "01" when(out_tx_dst_rdy0 = '1' and flu_distrib_next = '1') else
   --                     "10" when(out_tx_dst_rdy1 = '1' and flu_distrib_next = '1') else
   --                     "00";

   --! Distribution mask
   distrib_mask_genp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            flu_distrib_mask <= "01";
         else
            if(flu_distrib_next = '1' and flu_distrib_rdy = '1')then
               flu_distrib_mask(0) <= flu_distrib_mask(1);
               flu_distrib_mask(1) <= flu_distrib_mask(0);
            end if;
         end if;
      end if;
   end process;

   --! Distribution selection ready
  -- flu_distrib_rdy <= in_rx_sop and in_rx_src_rdy and
  --                    (out_tx_dst_rdy0 or out_tx_dst_rdy1);

   --! Distribution selection ready
   flu_distrib_rdy <= in_rx_sop and in_rx_src_rdy;

   --! Generation of distributed to
   distributed_to_out <= '0' when(flu_distrib_mask = "01")
                        else '1';

   -- -----------------------------------------------------
   -- Output signamp map
   -- -----------------------------------------------------
   TX_DATA0          <= out_tx_data0;
   TX_SOP_POS0       <= out_tx_sop_pos0;
   TX_EOP_POS0       <= out_tx_eop_pos0;
   TX_SOP0           <= out_tx_sop0;
   TX_EOP0           <= out_tx_eop0;
   TX_SRC_RDY0       <= out_tx_src_rdy0;
   out_tx_dst_rdy0   <= TX_DST_RDY0;

   TX_DATA1          <= out_tx_data1;
   TX_SOP_POS1       <= out_tx_sop_pos1;
   TX_EOP_POS1       <= out_tx_eop_pos1;
   TX_SOP1           <= out_tx_sop1;
   TX_EOP1           <= out_tx_eop1;
   TX_SRC_RDY1       <= out_tx_src_rdy1;
   out_tx_dst_rdy1   <= TX_DST_RDY1;

end architecture FULL;
