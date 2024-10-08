--
-- binder_a10_ent.vhd: Binder 10 component for Frame Link Unaligned (ALIGNED)
-- Copyright (C) 2014 CESNET
-- Author: Tomas Zavodnik <zavodnik@cesnet.cz>
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
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLUA_BINDER_10_EFF is

   --! Conversion function from STD_LOGIC to boolean
   function To_Boolean(L: std_logic) return boolean is
   begin
      if(L = '1')then
         return true;
      else
         return false;
      end if;
   end function;

   function To_Integer(L: boolean) return integer is
   begin
      if(L = true)then
         return 1;
      else
         return 0;
      end if;
   end function;

   function get_index(i: integer) return integer is
   begin
      if(i <= 4) then
         return i;
      else
         return i+6;
      end if;
   end function;

   constant HDR_INSERT_EN : boolean := (HDR_ENABLE and HDR_INSERT);
   constant IDATA_PIPE_EN : boolean := To_Boolean(PIPELINE_MAP(5));
   constant IHEAD_PIPE_DISABLE : boolean := not(To_Boolean(PIPELINE_MAP(5)) and (HDR_ENABLE and not(HDR_INSERT)));

   constant HDR_PARALL_EN : integer := To_Integer(HDR_ENABLE and not(HDR_INSERT));
   constant BINDER_PIPE : integer := conv_integer(PIPELINE_MAP(4 downto 0));
   constant BINDER_DSP  : integer := conv_integer(DSP_MAP);

   signal rx_hdr_dst_rdy_ins  : std_logic_vector(9 downto 0);
   signal rx_hdr_dst_rdy_pipe : std_logic_vector(9 downto 0);

   signal data_i     : std_logic_vector(16*DATA_WIDTH-1 downto 0);
   signal sop_pos_i  : std_logic_vector(16*SOP_POS_WIDTH-1 downto 0);
   signal eop_pos_i  : std_logic_vector(16*log2(DATA_WIDTH/8)-1 downto 0);
   signal sop_i      : std_logic_vector(16-1 downto 0);
   signal eop_i      : std_logic_vector(16-1 downto 0);
   signal src_rdy_i  : std_logic_vector(16-1 downto 0);
   signal dst_rdy_i  : std_logic_vector(16-1 downto 0);

   signal hdr_data_i    : std_logic_vector(16*HDR_WIDTH-1 downto 0);
   signal hdr_src_rdy_i : std_logic_vector(16-1 downto 0);
   signal hdr_dst_rdy_i : std_logic_vector(16-1 downto 0);

   signal selected_from_i  : std_logic_vector(4 downto 0);
   signal distributed_to_i : std_logic_vector(15 downto 0);

begin

   RX_HDR_DST_RDY <= rx_hdr_dst_rdy_ins when (HDR_INSERT = true) else rx_hdr_dst_rdy_pipe;

   HDR_INS_GEN:for i in 0 to 9 generate
      --! \brief Header insert
      HDR_INS_I: entity work.FLUA_HEADER_INSERT
      generic map(
         --! FLU configuration
         DATA_WIDTH    => DATA_WIDTH,
         SOP_POS_WIDTH => SOP_POS_WIDTH,

         --! Enable/Disable header insertion
         --!   false - Disable Header insertion
         --!   true  - Enable Header insertion
         HDR_ENABLE    => HDR_INSERT_EN,
         --! Widht of the header (multiple of 8)
         HDR_WIDTH     => HDR_WIDTH,

         -- Pipeline Config ------------------------
         -- Use input pipe
         OUT_PIPE_EN   => IDATA_PIPE_EN
      )
      port map(
         --! \name  Common interface
         RESET          => RESET,
         CLK            => CLK,

         --! \name Frame Link Unaligned (ALIGNED) input interface
         RX_DATA        => RX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
         RX_SOP_POS     => RX_SOP_POS((i+1)*SOP_POS_WIDTH-1 downto i*SOP_POS_WIDTH),
         RX_EOP_POS     => RX_EOP_POS((i+1)*log2(DATA_WIDTH/8)-1 downto i*log2(DATA_WIDTH/8)),
         RX_SOP         => RX_SOP(i),
         RX_EOP         => RX_EOP(i),
         RX_SRC_RDY     => RX_SRC_RDY(i),
         RX_DST_RDY     => RX_DST_RDY(i),

         --! \name Header input interface
         RX_HDR_DATA    => RX_HDR_DATA((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH),
         RX_HDR_SRC_RDY => RX_HDR_SRC_RDY(i),
         RX_HDR_DST_RDY => rx_hdr_dst_rdy_ins(i),

         --! \name Frame Link Unaligned (ALIGNED) output interface
         TX_DATA        => data_i((get_index(i)+1)*DATA_WIDTH-1 downto get_index(i)*DATA_WIDTH),
         TX_SOP_POS     => sop_pos_i((get_index(i)+1)*SOP_POS_WIDTH-1 downto get_index(i)*SOP_POS_WIDTH),
         TX_EOP_POS     => eop_pos_i((get_index(i)+1)*log2(DATA_WIDTH/8)-1 downto get_index(i)*log2(DATA_WIDTH/8)),
         TX_SOP         => sop_i(get_index(i)),
         TX_EOP         => eop_i(get_index(i)),
         TX_SRC_RDY     => src_rdy_i(get_index(i)),
         TX_DST_RDY     => dst_rdy_i(get_index(i))
      );

      data_i(11*DATA_WIDTH-1 downto 5*DATA_WIDTH) <= (others => '0');
      sop_pos_i(11*SOP_POS_WIDTH-1 downto 5*SOP_POS_WIDTH) <= (others => '0');
      eop_pos_i(11*log2(DATA_WIDTH/8)-1 downto 5*log2(DATA_WIDTH/8)) <= (others => '0');
      sop_i(10 downto 5) <= (others => '0');
      eop_i(10 downto 5) <= (others => '0');
      src_rdy_i(10 downto 5) <= (others => '0');

      --! \brief Input Header pipeline
      HDR_INS_HDR_PIPE_I:entity work.FLU_PIPE
      generic map(
         -- FrameLinkUnaligned Data Width
         DATA_WIDTH     => HDR_WIDTH,
         SOP_POS_WIDTH  => 1,
         USE_OUTREG     => true,
         FAKE_PIPE      => IHEAD_PIPE_DISABLE
      )
      port map(
         -- Common interface
         CLK            => CLK,
         RESET          => RESET,

         -- Input interface
         RX_DATA       => RX_HDR_DATA((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH),
         RX_SOP_POS    => (others=>'0'),
         RX_EOP_POS    => (others=>'1'),
         RX_SOP        => '1',
         RX_EOP        => '1',
         RX_SRC_RDY    => RX_HDR_SRC_RDY(i),
         RX_DST_RDY    => rx_hdr_dst_rdy_pipe(i),

         -- Output interface
         TX_DATA       => hdr_data_i((get_index(i)+1)*HDR_WIDTH-1 downto get_index(i)*HDR_WIDTH),
         TX_SOP_POS    => open,
         TX_EOP_POS    => open,
         TX_SOP        => open,
         TX_EOP        => open,
         TX_SRC_RDY    => hdr_src_rdy_i(get_index(i)),
         TX_DST_RDY    => hdr_dst_rdy_i(get_index(i))
      );

      hdr_data_i(11*HDR_WIDTH-1 downto 5*HDR_WIDTH) <= (others => '0');
      hdr_src_rdy_i(10 downto 5) <= (others => '0');
   end generate;

   DATA_BINDER_I: entity work.FLU_BINDER_EFF
   generic map(
      --! FLU configuration
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,

      --! Number of input ports
      --! \brief Warning, only powers of two are allowed as
      --! input port count. Minimal input ports are 2.
      INPUT_PORTS    => 16,

      --! Pipeline stages map (number of stages can be computed as log2(2*INPUT_PORTS)
      --!  '0' - pipeline won't be inserted
      --!  '1' - pipeline will be inserted
      PIPELINE_MAP   => BINDER_PIPE,

      --! DSP multiplexer map, it tells to RR element if to choose a DSP based multiplexor
      --! in the RR stage. Width and usage is similar to PIPELINE_MAP.
      --!   '0' - don't use the DSP multiplexor
      --!   '1' - use the DSP multiplexor
      DSP_MAP        => BINDER_DSP,

      --! Input Align map (It tells if input flow is aligned - can be computed as INPUT_PORTS)
      --!   '0' - input FLU flow is not alligned
      --!   '1' - input flow is alligned
      ALIGN_MAP    => 0,

      --! Logarithm base
      --! \brief Number of inputs of one stage multiplexer. These multiplexers
      --! create a RR selection tree. Therefore, number of stages is computed as
      --! log2(INPUT_PORTS)/log2(DIVISION_RATIO) + 1
      --! The result of this equation has to be an integer!
      --! Default value is 2
      DIVISION_RATIO => DIVISION_RATIO,

      --! Enable/Disable header (which can be assigned to input FLU frame)
      --!   0 - Disable Header function
      --!   1 - Enable Header function
      HDR_ENABLE     => HDR_PARALL_EN,
      --! Widht of the header
      HDR_WIDTH      => HDR_WIDTH,
      --! FIFO configuration
      HDR_FIFO_ITEMS    => HDR_FIFO_ITEMS,

      --! Enable/disable the reservation of 128 bit gap
      --! NOTICE: If you enable this functionality, you should be sure
      --! that the minimal packet length is of the frame is 60 bytes.
      --! This generic is tightly bounded with usage in network module and
      --! the FSM needs to be optimized for that usage. This generic can
      --! be used with DATA_WIDTH equals to 256 and 512 bits, because the
      --! author wants to keep the solution as simple as possible.
      --!   0 - Disable insertion of the 128 bit gap between FLU frames
      --!   1 - Enable insertion of the 128 bit gap between FLU frames
      RESERVE_GAP_EN    => RESERVE_GAP_EN,

      --! Enable/disable the debug interface (enabled by default)
      --! When disabled, output is not connected and some resources can be saved.
      --! Affected outputs are DISTRIBUTED_TO and SELECTED_FROM
      --!   0 - Disable debug
      --!   1 - Enable debug
      ENABLE_DEBUG      => ENABLE_DEBUG
   )
   port map(
         --! \name  Common interface
      RESET          => RESET,
      CLK            => CLK,

      --! \name Frame Link Unaligned input interface
      RX_DATA        => data_i,
      RX_SOP_POS     => sop_pos_i,
      RX_EOP_POS     => eop_pos_i,
      RX_SOP         => sop_i,
      RX_EOP         => eop_i,
      RX_SRC_RDY     => src_rdy_i,
      RX_DST_RDY     => dst_rdy_i,

      --! \name Header input interface
      RX_HDR_DATA        => hdr_data_i,
      RX_HDR_SRC_RDY     => hdr_src_rdy_i,
      RX_HDR_DST_RDY     => hdr_dst_rdy_i,

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA        => TX_DATA,
      TX_SOP_POS     => TX_SOP_POS,
      TX_EOP_POS     => TX_EOP_POS,
      TX_SOP         => TX_SOP,
      TX_EOP         => TX_EOP,
      TX_SRC_RDY     => TX_SRC_RDY,
      TX_DST_RDY     => TX_DST_RDY,

      --! \name Header output interface
      TX_HDR_DATA        => TX_HDR_DATA,
      TX_HDR_SRC_RDY     => TX_HDR_SRC_RDY,
      TX_HDR_DST_RDY     => TX_HDR_DST_RDY,

      --! \name Debug
      SELECTED_FROM  => selected_from_i,
      --! Information abou internal distribution interface (one bit on interface)
      DISTRIBUTED_TO => distributed_to_i
   );

   with selected_from_i(4 downto 1) select
      SELECTED_FROM  <= "0000000001" & selected_from_i(0) when "0000",
                        "0000000010" & selected_from_i(0) when "0001",
                        "0000000100" & selected_from_i(0) when "0010",
                        "0000001000" & selected_from_i(0) when "0011",
                        "0000010000" & selected_from_i(0) when "0100",
                        "0000100000" & selected_from_i(0) when "1011",
                        "0001000000" & selected_from_i(0) when "1100",
                        "0010000000" & selected_from_i(0) when "1101",
                        "0100000000" & selected_from_i(0) when "1110",
                        "1000000000" & selected_from_i(0) when "1111",
                        (others => 'X') when others;

   DISTRIBUTED_TO <= distributed_to_i(15 downto 11) & distributed_to_i(4 downto 0);

end architecture FULL;
