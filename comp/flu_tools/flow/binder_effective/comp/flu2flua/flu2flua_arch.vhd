--
-- flu2flua_arch.vhd: Component for conversion of FLU to Aligned FLU
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLU2FLUA is

   --! Source and destination ready signasl
   signal tx_src_rdy0_sig   : std_logic;
   signal tx_src_rdy0_out   : std_logic;
   signal tx_dst_rdy0_sig   : std_logic;
   signal tx_dst_rdy0_in    : std_logic;

   signal tx_src_rdy1_sig   : std_logic;
   signal tx_src_rdy1_out   : std_logic;
   signal tx_dst_rdy1_sig   : std_logic;
   signal tx_dst_rdy1_in    : std_logic;

   signal tx_hdr_src_rdy_out  : std_logic;
   signal tx_hdr_dst_rdy_sig  : std_logic;

   --! SOP signal
   signal tx_sop0_sig   : std_logic;
   signal tx_sop1_sig   : std_logic;

   --! Header data
   signal tx_hdr_data_out  : std_logic_vector(HDR_WIDTH-1 downto 0);

   signal hdr_enable_wr          : std_logic;
   signal hdr_enable_full        : std_logic;
   signal hdr_enable_read_req    : std_logic;
   signal hdr_enable_empty       : std_logic;
   signal hdr_enable_out         : std_logic_vector(0 downto 0);
   signal hdr_enable_in          : std_logic_vector(0 downto 0);

   signal flu2flua_distrib_to    : std_logic;

   signal flu2flua_sop           : std_logic;
   signal flu2flua_src_rdy       : std_logic;
   signal flu2flua_src_rdy_sig   : std_logic;
   signal flu2flua_dst_rdy       : std_logic;
   signal flu2flua_dst_rdy_sig   : std_logic;

   signal enabled_lane0          : std_logic;
   signal enabled_lane1          : std_logic;

begin

-- ----------------------------------------------------------------------------
--                        FLU --> FLUA
-- ----------------------------------------------------------------------------
FLU2FLUA_CORE_I:entity work.FLU2FLUA_CORE
   generic map(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,

      -- Pipeline Config ------------------------
      -- Use input pipe
      IN_PIPE_EN           => IN_PIPE_EN,
      -- Input pipe type (SHREG or REG)
      IN_PIPE_TYPE         => IN_PIPE_TYPE,
      -- Use output register of input pipe
      IN_PIPE_OUTREG       => IN_PIPE_OUTREG,
      -- Use output pipe
      OUT_PIPE_EN          => OUT_PIPE_EN,
      -- Output pipe type (SHREG or REG)
      OUT_PIPE_TYPE        => OUT_PIPE_TYPE,
      -- Use output register of input pipe
      OUT_PIPE_OUTREG      => OUT_PIPE_OUTREG,
      -- Select PIPE component implementation: "REG" or "SHREG"
      PIPE_TYPE            => PIPE_TYPE,
      -- Base ID
      ENABLE_DEBUG         => ENABLE_DEBUG,
      ID_WIDTH             => ID_WIDTH,
      ID0_VAL              => ID0_VAL,
      ID1_VAL              => ID1_VAL,

      -- Align input flow
      ALIGN                => ALIGN
   )
   port map(
       -- Common interface
      RESET          => RESET,
      CLK            => CLK,

      -- Frame Link Unaligned input interface
      RX_DATA        => RX_DATA,
      RX_SOP_POS     => RX_SOP_POS,
      RX_EOP_POS     => RX_EOP_POS,
      RX_SOP         => flu2flua_sop,
      RX_EOP         => RX_EOP,
      RX_SRC_RDY     => flu2flua_src_rdy_sig,
      RX_DST_RDY     => flu2flua_dst_rdy,

      -- Distributed to output (active when SOP = 1)
      DISTRIBUTED_TO => flu2flua_distrib_to,

      -- Frame Link Unaligned output lane 0
      TX_DATA0       => TX_DATA0,
      TX_SOP_POS0    => TX_SOP_POS0,
      TX_EOP_POS0    => TX_EOP_POS0,
      TX_SOP0        => tx_sop0_sig,
      TX_EOP0        => TX_EOP0,
      TX_SRC_RDY0    => tx_src_rdy0_out,
      TX_DST_RDY0    => tx_dst_rdy0_sig,
      ID0            => ID0,

      -- Frame Link Unaligned output lane 1
      TX_DATA1       => TX_DATA1,
      TX_SOP_POS1    => TX_SOP_POS1,
      TX_EOP_POS1    => TX_EOP_POS1,
      TX_SOP1        => tx_sop1_sig,
      TX_EOP1        => TX_EOP1,
      TX_SRC_RDY1    => tx_src_rdy1_out,
      TX_DST_RDY1    => tx_dst_rdy1_sig,
      ID1            => ID1
   );

   --! Map of output/input signals
   ENABLE_DISTRIBUTE_TO:if(ENABLE_DEBUG = 1)generate
      DISTRIBUTED_TO    <= flu2flua_distrib_to;
   end generate;

   flu2flua_sop      <= RX_SOP;
   flu2flua_src_rdy  <= RX_SRC_RDY;
   RX_DST_RDY        <= flu2flua_dst_rdy_sig;

   --! Generation of desination and source ready
   flu2flua_src_rdy_sig <= (not(hdr_enable_full) and flu2flua_sop and flu2flua_src_rdy) or
                           (not(flu2flua_sop) and flu2flua_src_rdy);

   flu2flua_dst_rdy_sig <= (not(hdr_enable_full) and flu2flua_sop and flu2flua_dst_rdy) or
                           (not(flu2flua_sop) and flu2flua_dst_rdy);

-- ----------------------------------------------------------------------------
--                        Header FIFO
-- ----------------------------------------------------------------------------
   HDR_FIFO_GEN:if(HDR_ENABLE = 1 and ALIGN = true)generate

      --! Header signal connection
      tx_hdr_data_out <= RX_HDR_DATA;
      tx_hdr_src_rdy_out <= RX_HDR_SRC_RDY;
      RX_HDR_DST_RDY <= tx_hdr_dst_rdy_sig;

      --! Enable FIFO for header synchronization
      ENABLE_FIFO_I:entity work.FIFO
         generic map(
            -- Set data width here
            DATA_WIDTH     => 1,

            -- Set number of items in FIFO here
            ITEMS          => HDR_FIFO_ITEMS
         )
         port map(
            RESET    => RESET,
            CLK      => CLK,

            -- Write interface
            DATA_IN     => hdr_enable_in,
            WRITE_REQ   => hdr_enable_wr,
            FULL        => hdr_enable_full,
            LSTBLK      => open,

            -- Read interface
            DATA_OUT    => hdr_enable_out,
            READ_REQ    => hdr_enable_read_req,
            EMPTY       => hdr_enable_empty
         );

         -- Map of input enable signal
         hdr_enable_in(0)  <= flu2flua_distrib_to;
         hdr_enable_wr     <= flu2flua_sop and flu2flua_src_rdy_sig and flu2flua_dst_rdy_sig;

         -- Output header data map
         TX_HDR_DATA0 <= tx_hdr_data_out;
         TX_HDR_DATA1 <= tx_hdr_data_out;

         enabled_lane0 <= not(hdr_enable_out(0)) and not(hdr_enable_empty);
         enabled_lane1 <= hdr_enable_out(0) and not(hdr_enable_empty);
   end generate;

   HDR_NO_FIFO_GEN:if(HDR_ENABLE = 1 and ALIGN = false)generate
      TX_HDR_DATA0 <= RX_HDR_DATA;
      TX_HDR_DATA1 <= (others=>'0');
      tx_hdr_src_rdy_out <= RX_HDR_SRC_RDY;
      RX_HDR_DST_RDY <= tx_hdr_dst_rdy_sig;
      hdr_enable_full <= '0';
      hdr_enable_empty <= '0';

      enabled_lane0 <= '1';
      enabled_lane1 <= '0';
  end generate;

   NO_HDR_NO_ALIGN_GEN:if(HDR_ENABLE = 0 and ALIGN = true)generate
      -- HW accelerated /dev/NUll
      TX_HDR_DATA0 <= (others=>'0');
      TX_HDR_DATA1 <= (others=>'0');
      tx_hdr_src_rdy_out <= '1';
      RX_HDR_DST_RDY <= '1';
      hdr_enable_full <= '0';
      hdr_enable_empty <= '0';

      enabled_lane0 <= '1';
      enabled_lane1 <= '1';
   end generate;

   NO_HDR_ALIGN_GEN:if(HDR_ENABLE = 0 and ALIGN = false)generate
      -- HW accelerated /dev/NUll
      TX_HDR_DATA0 <= (others=>'0');
      TX_HDR_DATA1 <= (others=>'0');
      RX_HDR_DST_RDY <= '1';
      tx_hdr_src_rdy_out <= '1';
      hdr_enable_full <= '0';
      hdr_enable_empty <= '0';

      enabled_lane0 <= '1';
      enabled_lane1 <= '0';
   end generate;

-- ----------------------------------------------------------------------------
--                        Output signal map
-- ----------------------------------------------------------------------------

   --! Map of output signals from/to FLU2FLUA_CORE
   TX_SOP0 <= tx_sop0_sig;
   TX_SOP1 <= tx_sop1_sig;
   TX_SRC_RDY0 <= tx_src_rdy0_sig;
   TX_SRC_RDY1 <= tx_src_rdy1_sig;
   tx_dst_rdy0_in <= TX_DST_RDY0;
   tx_dst_rdy1_in <= TX_DST_RDY1;

-- ----------------------------------------------------------------------------
--                        DATA/HEADER synchronization logic
-- ----------------------------------------------------------------------------
-- We need to synchronize output of the header FIFO with start of the FLU frame

-- Destination/Source ready for data lane 0
tx_dst_rdy0_sig <= (tx_hdr_src_rdy_out and (tx_sop0_sig and tx_src_rdy0_out) and tx_dst_rdy0_in and enabled_lane0) or
                   (not(tx_sop0_sig) and tx_dst_rdy0_in);

tx_src_rdy0_sig <= (tx_hdr_src_rdy_out and (tx_sop0_sig and tx_src_rdy0_out) and enabled_lane0) or
                   (not(tx_sop0_sig) and tx_src_rdy0_out);

-- Destination/Source ready for lane 1
tx_dst_rdy1_sig <= (tx_hdr_src_rdy_out and (tx_sop1_sig and tx_src_rdy1_out) and tx_dst_rdy1_in and enabled_lane1) or
                   (not(tx_sop1_sig) and tx_dst_rdy1_in);

tx_src_rdy1_sig <= (tx_hdr_src_rdy_out and (tx_sop1_sig and tx_src_rdy1_out) and enabled_lane1) or
                   (not(tx_sop1_sig) and tx_src_rdy1_out);

-- Destination/Source ready for header lane
tx_hdr_dst_rdy_sig <= (tx_hdr_src_rdy_out and (tx_sop0_sig and tx_src_rdy0_out) and tx_dst_rdy0_in and enabled_lane0) or
                      (tx_hdr_src_rdy_out and (tx_sop1_sig and tx_src_rdy1_out) and tx_dst_rdy1_in and enabled_lane1);

-- Reading from the synchronization FIFO is as same as for header FIFO
hdr_enable_read_req <= tx_hdr_dst_rdy_sig;

end architecture FULL;
