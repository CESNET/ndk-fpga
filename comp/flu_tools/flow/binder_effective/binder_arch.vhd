--
-- binder_arch.vhd: Binder N-1 component for Frame Link Unaligned
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
use IEEE.std_logic_arith.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLU_BINDER_EFF is
   --! Conversion function from STD_LOGIC to boolean
   function To_Boolean(L: std_logic) return boolean is
   begin
      if(L = '1')then
         return true;
      else
         return false;
      end if;
   end function;

   --! Function to get port index
   function Get_Port(i : integer) return integer is
   begin
      return (i+INPUT_PORTS/2) mod INPUT_PORTS;
   end function;

   -- Constant declarations ---------------------------------------------------
   --! FLU2FLUA Pipeline configuration
   constant FLU2FLUA_IN_PIPE_EN           : boolean := true;
   constant FLU2FLUA_IN_PIPE_OUTREG       : boolean := false;
   constant FLU2FLUA_OUT_PIPE_EN          : boolean := true;
   constant FLU2FLUA_OUT_PIPE_OUTREG      : boolean := false;

   --! FLUA Binder configuration
   constant FLUA_BINDER_OUT_PIPE_OUTREG      : boolean := false;

   --! RR_FLUA configuration (WARNING - don't change this value)
   constant RR_INPUTS            : integer := DIVISION_RATIO;

   --! EOP_POS bus width
   constant EOP_POS_WIDTH        : integer := log2(DATA_WIDTH/8);

   --! Real number of input ports
   constant REAL_PORT_COUNT   : integer := 2*INPUT_PORTS;

   --! Number of RR selection stages
   constant RR_STAGES         : integer := log2(INPUT_PORTS)/log2(DIVISION_RATIO) + 1;

   --! ID Width
   constant ID_WIDTH          : integer := log2(INPUT_PORTS)+1;

   --! STD_LOGIC pippeline map
   constant PIPELINE_MAP_STD  : std_logic_vector :=
      conv_std_logic_vector(PIPELINE_MAP,RR_STAGES);

   --! STD_LOGIC align map
   constant ALIGN_MAP_STD     : std_logic_vector :=
      conv_std_logic_vector(ALIGN_MAP,INPUT_PORTS);

   --! STD_LOGIC DSP stage map
   constant DSP_MAP_STD       : std_logic_vector :=
      conv_std_logic_vector(DSP_MAP,RR_STAGES);

   --! RR stage data type (last line is final data type)
   type rr_data_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT*DATA_WIDTH-1 downto 0);

   --! RR stage sop type (last line is final data type)
   type rr_sop_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT-1 downto 0);

   --! RR stage sop pos type (last line is final data type)
   type rr_sop_pos_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT*SOP_POS_WIDTH-1 downto 0);

   --! RR stage eop type (last line is final data type)
   type rr_eop_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT-1 downto 0);

   --! RR stage eop pos type (last line is final data type)
   type rr_eop_pos_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT*EOP_POS_WIDTH-1 downto 0);

   --! RR stage src_rdy type (last line is final data type)
   type rr_src_rdy_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT-1 downto 0);

   --! RR stage dst_rdy type (last line is final data type)
   type rr_dst_rdy_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT-1 downto 0);

   --! RR stage for selected ID
   type rr_id_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT*ID_WIDTH downto 0);

   --! RR Stage of Header data
   type rr_hdr_stages is array(0 to RR_STAGES-1) of
      std_logic_vector(REAL_PORT_COUNT*HDR_WIDTH-1 downto 0);

   -- Signal declarations -----------------------------------------------------
   --! FLU RR stages
   signal rr_data          : rr_data_stages;
   signal rr_sop           : rr_sop_stages;
   signal rr_eop           : rr_eop_stages;
   signal rr_sop_pos       : rr_sop_pos_stages;
   signal rr_eop_pos       : rr_eop_pos_stages;
   signal rr_src_rdy       : rr_src_rdy_stages;
   signal rr_dst_rdy       : rr_dst_rdy_stages;
   signal rr_id            : rr_id_stages;
   signal rr_hdr           : rr_hdr_stages;


   --! From FLUA binder to BINDER_SYNC
   signal sync_rx_hdr_data    : std_logic_vector(HDR_WIDTH-1 downto 0);
   signal sync_rx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sync_rx_sop_pos     : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal sync_rx_eop_pos     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal sync_rx_sop         : std_logic;
   signal sync_rx_eop         : std_logic;
   signal sync_rx_src_rdy     : std_logic;
   signal sync_rx_dst_rdy     : std_logic;

   signal pipe_tx_data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal pipe_tx_sop_pos     : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal pipe_tx_eop_pos     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal pipe_tx_sop         : std_logic;
   signal pipe_tx_eop         : std_logic;
   signal pipe_tx_src_rdy     : std_logic;
   signal pipe_tx_dst_rdy     : std_logic;

   --! Header destination is ready (this signal is set to pernament 1 when no
   --! header is inserted)
   signal pipe_tx_hdr_dst_rdy   : std_logic;
   signal pipe_tx_hdr_src_rdy   : std_logic;
   signal pipe_tx_hdr_data    : std_logic_vector(HDR_WIDTH-1 downto 0);

begin

   -- Generate input FLU->FLUA connections
   FLU_TO_FLUA_GEN:for i in 0 to INPUT_PORTS-1 generate
   FLU_TO_FLUA_I:entity work.FLU2FLUA
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,

         -- Pipeline Config ------------------------
         -- Use input pipe
         IN_PIPE_EN           => FLU2FLUA_IN_PIPE_EN,
         -- Input pipe type
         IN_PIPE_TYPE         => PIPE_TYPE,
         -- Use output register of input pipe
         IN_PIPE_OUTREG       => FLU2FLUA_IN_PIPE_OUTREG,
         -- Use output pipe
         OUT_PIPE_EN          => FLU2FLUA_OUT_PIPE_EN,
         -- Outnput pipe type
         OUT_PIPE_TYPE        => PIPE_TYPE,
         -- Use output register of input pipe
         OUT_PIPE_OUTREG      => FLU2FLUA_OUT_PIPE_OUTREG,
         -- Select type of PIPE implementation: "SHREG" or "REG"
         PIPE_TYPE            => PIPE_TYPE,
         -- Base ID
         -- DISTRIBUTED_TO output will be disabled too
         ENABLE_DEBUG         => ENABLE_DEBUG,
         ID_WIDTH             => ID_WIDTH,
         ID0_VAL              => 2*i,
         ID1_VAL              => 2*i+1,

         -- Align output flow
         ALIGN                => To_Boolean(ALIGN_MAP_STD(i)),

         --! Enable/Disable header (which can be assigned to input FLU frame)
         --!   0 - Disable Header function
         --!   1 - Enable Header function
         HDR_ENABLE           => HDR_ENABLE,
         --! Widht of the header
         HDR_WIDTH            => HDR_WIDTH,
         --! Header FIFO configuration
         HDR_FIFO_ITEMS       => HDR_FIFO_ITEMS
      )
      port map(
          -- Common interface
         RESET          => RESET,
         CLK            => CLK,

         -- Frame Link Unaligned input interface
         RX_DATA        => RX_DATA((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
         RX_SOP_POS     => RX_SOP_POS((i+1)*SOP_POS_WIDTH-1 downto i*SOP_POS_WIDTH),
         RX_EOP_POS     => RX_EOP_POS((i+1)*EOP_POS_WIDTH-1 downto i*EOP_POS_WIDTH),
         RX_SOP         => RX_SOP(i),
         RX_EOP         => RX_EOP(i),
         RX_SRC_RDY     => RX_SRC_RDY(i),
         RX_DST_RDY     => RX_DST_RDY(i),

         -- Header input interface
         RX_HDR_DATA    => RX_HDR_DATA((i+1)*HDR_WIDTH-1 downto i*HDR_WIDTH),
         RX_HDR_SRC_RDY => RX_HDR_SRC_RDY(i),
         RX_HDR_DST_RDY => RX_HDR_DST_RDY(i),

         -- Distributed to output (active when SOP = 1)
         DISTRIBUTED_TO => DISTRIBUTED_TO(i),

         -- Frame Link Unaligned output lane 0
         TX_DATA0       => rr_data(0)((2*i+1)*DATA_WIDTH-1 downto (2*i)*DATA_WIDTH),
         TX_HDR_DATA0   => rr_hdr(0)((2*i+1)*HDR_WIDTH-1 downto (2*i)*HDR_WIDTH),
         TX_SOP_POS0    => rr_sop_pos(0)((2*i+1)*SOP_POS_WIDTH-1 downto (2*i)*SOP_POS_WIDTH),
         TX_EOP_POS0    => rr_eop_pos(0)((2*i+1)*EOP_POS_WIDTH-1 downto (2*i)*EOP_POS_WIDTH),
         TX_SOP0        => rr_sop(0)(2*i),
         TX_EOP0        => rr_eop(0)(2*i),
         TX_SRC_RDY0    => rr_src_rdy(0)(2*i),
         TX_DST_RDY0    => rr_dst_rdy(0)(2*i),
         ID0            => rr_id(0)((2*i+1)*ID_WIDTH-1 downto (2*i)*ID_WIDTH),

         -- Frame Link Unaligned output lane 1
         TX_DATA1       => rr_data(0)((2*Get_Port(i)+2)*DATA_WIDTH-1 downto (2*Get_Port(i)+1)*DATA_WIDTH),
         TX_HDR_DATA1   => rr_hdr(0)((2*Get_Port(i)+2)*HDR_WIDTH-1 downto (2*Get_Port(i)+1)*HDR_WIDTH),
         TX_SOP_POS1    => rr_sop_pos(0)((2*Get_Port(i)+2)*SOP_POS_WIDTH-1 downto (2*Get_Port(i)+1)*SOP_POS_WIDTH),
         TX_EOP_POS1    => rr_eop_pos(0)((2*Get_Port(i)+2)*EOP_POS_WIDTH-1 downto (2*Get_Port(i)+1)*EOP_POS_WIDTH),
         TX_SOP1        => rr_sop(0)(2*Get_Port(i)+1),
         TX_EOP1        => rr_eop(0)(2*Get_Port(i)+1),
         TX_SRC_RDY1    => rr_src_rdy(0)(2*Get_Port(i)+1),
         TX_DST_RDY1    => rr_dst_rdy(0)(2*Get_Port(i)+1),
         ID1            => rr_id(0)((2*Get_Port(i)+2)*ID_WIDTH-1 downto (2*Get_Port(i)+1)*ID_WIDTH)
      );
      end generate;

   -- Generate RR selection tree
   RR_SEL_TREE_GEN:for i in 1 to RR_STAGES-1 generate
      -- For all stages ...
      RR_SEL_PORT_GEN:for j in 0 to (2*INPUT_PORTS)/(DIVISION_RATIO**(i))-1 generate
         RR_FLUA_SELECT_I:entity work.RR_SELECT
            generic map(
               -- FLU Config -----------------------------
               --! FLU protocol generics
               DATA_WIDTH     => DATA_WIDTH,
               SOP_POS_WIDTH  => SOP_POS_WIDTH,
               --! Number of input input interfaces
               INPUTS         => RR_INPUTS,

               --! Width of information ID
               ID_WIDTH       => ID_WIDTH,
               ENABLE_ID      => ENABLE_DEBUG,
               -- Pipeline Config ------------------------
               -- Use input pipe
               OUT_PIPE_EN    => To_Boolean(PIPELINE_MAP_STD(i-1)),

               --! Enable/Disable header (which can be assigned to input FLU frame)
               --!   0 - Disable Header function
               --!   1 - Enable Header function
               HDR_ENABLE     => HDR_ENABLE,
               --! Widht of the header
               HDR_WIDTH      => HDR_WIDTH,

               --! Enable DSP multiplexing
               ENABLE_DSP     => To_Boolean(DSP_MAP_STD(i-1))
            )
            port map(
                -- -------------------------------------------------
                -- \name Common interface
                -- -------------------------------------------------
               RESET          => RESET,
               CLK            => CLK,

               -- --------------------------------------------------
               -- \name Frame Link Unaligned input interface
               -- --------------------------------------------------
               RX_DATA     => rr_data(i-1)((RR_INPUTS*j+RR_INPUTS)*DATA_WIDTH-1 downto (RR_INPUTS*j)*DATA_WIDTH),
               RX_SOP_POS  => rr_sop_pos(i-1)((RR_INPUTS*j+RR_INPUTS)*SOP_POS_WIDTH-1 downto (RR_INPUTS*j)*SOP_POS_WIDTH),
               RX_EOP_POS  => rr_eop_pos(i-1)((RR_INPUTS*j+RR_INPUTS)*EOP_POS_WIDTH-1 downto (RR_INPUTS*j)*EOP_POS_WIDTH),
               RX_SOP      => rr_sop(i-1)(RR_INPUTS*j+RR_INPUTS-1 downto RR_INPUTS*j),
               RX_EOP      => rr_eop(i-1)(RR_INPUTS*j+RR_INPUTS-1 downto RR_INPUTS*j),
               RX_SRC_RDY  => rr_src_rdy(i-1)(RR_INPUTS*j+RR_INPUTS-1 downto RR_INPUTS*j),
               RX_DST_RDY  => rr_dst_rdy(i-1)(RR_INPUTS*j+RR_INPUTS-1 downto RR_INPUTS*j),
               ID_IN       => rr_id(i-1)((RR_INPUTS*j+RR_INPUTS)*ID_WIDTH-1 downto (RR_INPUTS*j)*ID_WIDTH),
               RX_HDR      => rr_hdr(i-1)((RR_INPUTS*j+RR_INPUTS)*HDR_WIDTH-1 downto (RR_INPUTS*j)*HDR_WIDTH),

               -- --------------------------------------------------
               -- \name Frame Link Unaligned output interface
               -- --------------------------------------------------
               TX_DATA        => rr_data(i)((j+1)*DATA_WIDTH-1 downto j*DATA_WIDTH),
               TX_SOP_POS     => rr_sop_pos(i)((j+1)*SOP_POS_WIDTH-1 downto j*SOP_POS_WIDTH),
               TX_EOP_POS     => rr_eop_pos(i)((j+1)*EOP_POS_WIDTH-1 downto j*EOP_POS_WIDTH),
               TX_SOP         => rr_sop(i)(j),
               TX_EOP         => rr_eop(i)(j),
               TX_SRC_RDY     => rr_src_rdy(i)(j),
               TX_DST_RDY     => rr_dst_rdy(i)(j),
               ID_OUT         => rr_id(i)((j+1)*ID_WIDTH-1 downto j*ID_WIDTH),
               TX_HDR         => rr_hdr(i)((j+1)*HDR_WIDTH-1 downto j*HDR_WIDTH)
            );
      end generate; -- End of generate loop for all ports
   end generate; -- End of generate loop for all stages

   --! FLUA -> FLU binder
   FLUA_TO_FLU_BIND_I:entity work.FLUA_BINDER
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         ID_WIDTH       => ID_WIDTH,
         ENABLE_ID      => ENABLE_DEBUG,

         -- Pipeline Config ------------------------
         -- Use output pipe
         OUT_PIPE_EN          => To_Boolean(PIPELINE_MAP_STD(RR_STAGES-1)),
         -- Use output register of input pipe
         OUT_PIPE_OUTREG      => FLUA_BINDER_OUT_PIPE_OUTREG,

         --! Enable/Disable header (which can be assigned to input FLU frame)
         --!   0 - Disable Header function
         --!   1 - Enable Header function
         HDR_ENABLE        => HDR_ENABLE,
         --! Widht of the header
         HDR_WIDTH         => HDR_WIDTH,

         --! Enable/disable the reservation of 128 bit gap
         --! NOTICE: If you enable this functionality, you should be sure
         --! that the minimal length of the frame (in bytes) + 128/8 is
         --! bigger or equal to DATA_WIDTH/8. Because this functionality
         --! is tightly bounded with usage in network module and the
         --! FSM needs to be optimized for that usage.
         --!   0 - Disable insertion of the 128 bit gap between FLU frames
         --!   1 - Enable insertion of the 128 bit gap between FLU frames
         RESERVE_GAP_EN    => RESERVE_GAP_EN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         -- RX Lane 0
         RX_HDR_DATA0   => rr_hdr(RR_STAGES-1)(HDR_WIDTH-1 downto 0),
         RX_DATA0       => rr_data(RR_STAGES-1)(DATA_WIDTH-1 downto 0),
         RX_SOP_POS0    => rr_sop_pos(RR_STAGES-1)(SOP_POS_WIDTH-1 downto 0),
         RX_EOP_POS0    => rr_eop_pos(RR_STAGES-1)(EOP_POS_WIDTH-1 downto 0),
         RX_SOP0        => rr_sop(RR_STAGES-1)(0),
         RX_EOP0        => rr_eop(RR_STAGES-1)(0),
         RX_SRC_RDY0    => rr_src_rdy(RR_STAGES-1)(0),
         RX_DST_RDY0    => rr_dst_rdy(RR_STAGES-1)(0),
         ID0            => rr_id(RR_STAGES-1)(ID_WIDTH-1 downto 0),

         -- RX Lane 1
         RX_HDR_DATA1   => rr_hdr(RR_STAGES-1)(2*HDR_WIDTH-1 downto HDR_WIDTH),
         RX_DATA1       => rr_data(RR_STAGES-1)(2*DATA_WIDTH-1 downto DATA_WIDTH),
         RX_SOP_POS1    => rr_sop_pos(RR_STAGES-1)(2*SOP_POS_WIDTH-1 downto SOP_POS_WIDTH),
         RX_EOP_POS1    => rr_eop_pos(RR_STAGES-1)(2*EOP_POS_WIDTH-1 downto EOP_POS_WIDTH),
         RX_SOP1        => rr_sop(RR_STAGES-1)(1),
         RX_EOP1        => rr_eop(RR_STAGES-1)(1),
         RX_SRC_RDY1    => rr_src_rdy(RR_STAGES-1)(1),
         RX_DST_RDY1    => rr_dst_rdy(RR_STAGES-1)(1),
         ID1            => rr_id(RR_STAGES-1)(2*ID_WIDTH-1 downto ID_WIDTH),

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_HDR_DATA    => sync_rx_hdr_data,
         TX_DATA        => sync_rx_data,
         TX_SOP_POS     => sync_rx_sop_pos,
         TX_EOP_POS     => sync_rx_eop_pos,
         TX_SOP         => sync_rx_sop,
         TX_EOP         => sync_rx_eop,
         TX_SRC_RDY     => sync_rx_src_rdy,
         TX_DST_RDY     => sync_rx_dst_rdy,
         ID             => SELECTED_FROM
      );

   --! Output synchronzation unit which defend agains timing loops (this
   --! module doesn't implement any pipeline)
   BINDER_SYNC_I:entity work.BINDER_SYNC
   generic map(
      --! FLU configuration
      DATA_WIDTH     => DATA_WIDTH,
      SOP_POS_WIDTH  => SOP_POS_WIDTH,

      --! Header withd
      HDR_WIDTH      => HDR_WIDTH
   )
   port map(
       --! \name  Common interface
      RESET          => RESET,
      CLK            => CLK,

      --! \name Frame Link Unaligned input interface
      RX_HDR_DATA    => sync_rx_hdr_data,
      RX_DATA        => sync_rx_data,
      RX_SOP_POS     => sync_rx_sop_pos,
      RX_EOP_POS     => sync_rx_eop_pos,
      RX_SOP         => sync_rx_sop,
      RX_EOP         => sync_rx_eop,
      RX_SRC_RDY     => sync_rx_src_rdy,
      RX_DST_RDY     => sync_rx_dst_rdy,

      --! \name Frame Link Unaligned concentrated interface
      TX_DATA        => pipe_tx_data,
      TX_SOP_POS     => pipe_tx_sop_pos,
      TX_EOP_POS     => pipe_tx_eop_pos,
      TX_SOP         => pipe_tx_sop,
      TX_EOP         => pipe_tx_eop,
      TX_SRC_RDY     => pipe_tx_src_rdy,
      TX_DST_RDY     => pipe_tx_dst_rdy,

      --! \name Header output interface
      TX_HDR_DATA       => pipe_tx_hdr_data,
      TX_HDR_SRC_RDY    => pipe_tx_hdr_src_rdy,
      TX_HDR_DST_RDY    => pipe_tx_hdr_dst_rdy
   );

    -- If no header will be inserted --- destination is still ready
    NO_HDR_GEN:if(HDR_ENABLE = 0)generate
        pipe_tx_hdr_dst_rdy <= '1';
    end generate;

    HDR_GEN:if(HDR_ENABLE = 1)generate
        pipe_tx_i: entity work.FLU_PIPE_DEEPER
        generic map (
            DATA_WIDTH      => DATA_WIDTH,
            SOP_POS_WIDTH   => 3,
            USE_OUTREG      => true,
            FAKE_PIPE       => not OUTPUT_PIPE_EN
        ) port map (
            CLK             => CLK,
            RESET           => RESET,
            RX_DATA         => pipe_tx_data,
            RX_SOP_POS      => pipe_tx_sop_pos,
            RX_EOP_POS      => pipe_tx_eop_pos,
            RX_SOP          => pipe_tx_sop,
            RX_EOP          => pipe_tx_eop,
            RX_SRC_RDY      => pipe_tx_src_rdy,
            RX_DST_RDY      => pipe_tx_dst_rdy,
            TX_DATA         => TX_DATA,
            TX_SOP_POS      => TX_SOP_POS,
            TX_EOP_POS      => TX_EOP_POS,
            TX_SOP          => TX_SOP,
            TX_EOP          => TX_EOP,
            TX_SRC_RDY      => TX_SRC_RDY,
            TX_DST_RDY      => TX_DST_RDY
        );

        pipe_tx_hdr_i: entity work.PIPE_DEEPER
        generic map (
            DATA_WIDTH      => HDR_WIDTH,
            USE_OUTREG      => true,
            FAKE_PIPE       => not OUTPUT_PIPE_EN
        ) port map (
            CLK             => CLK,
            RESET           => RESET,
            IN_DATA         => pipe_tx_hdr_data,
            IN_SRC_RDY      => pipe_tx_hdr_src_rdy,
            IN_DST_RDY      => pipe_tx_hdr_dst_rdy,
            OUT_DATA        => TX_HDR_DATA,
            OUT_SRC_RDY     => TX_HDR_SRC_RDY,
            OUT_DST_RDY     => TX_HDR_DST_RDY
        );
    end generate;

end architecture FULL;
