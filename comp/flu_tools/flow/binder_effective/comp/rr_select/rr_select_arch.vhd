--
-- align_arch.vhd: FLU align component architecture
-- Copyright (C) 2014 CESNET
-- Author: Pavel Benacek <benacek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
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
architecture FULL of RR_SELECT is
   -- Constants declaration ---------------------------------------------------
   --! Blocking or nonblocking behaviour of the FLU multiplexer
   constant FLU_MUX_BLOCKING     : boolean := true;
   --! FLU Pipeline config
   constant FLU_PIPE_USE_OUTREG  : boolean := true;
   constant FLU_PIPE_FAKE_PIPE   : boolean := false;

   -- Signal declaration ------------------------------------------------------
      -- RR selection logic
   --! Output port is valid
   signal next_req_vld          : std_logic;

   --! Signals for round robin selection
   signal rr_req              : std_logic_vector(INPUTS-1 downto 0);
   signal rr_req_prev         : std_logic_vector(INPUTS-1 downto 0);
   signal rr_req_shifted      : std_logic_vector(INPUTS-1 downto 0);
   signal rr_req_masked       : std_logic_vector(INPUTS-1 downto 0);
   signal rr_req_mask         : std_logic_vector(INPUTS-1 downto 0);
   --! Extracted LSB grants
   signal rr_lsb_req_masked   : std_logic_vector(INPUTS-1 downto 0);
   signal rr_lsb_req          : std_logic_vector(INPUTS-1 downto 0);
   --! Output RR winner
   signal rr_req_win          : std_logic_vector(INPUTS-1 downto 0);

   --! Control signals for FLU multiplexer
   signal flu_mux_sel      : std_logic_vector(log2(INPUTS)-1 downto 0);
   signal flu_mux_sel_rdy  : std_logic;
   signal flu_mux_sel_nxt  : std_logic;

   --! ID output
   signal sel_id_out           : std_logic_vector(ID_WIDTH-1 downto 0);
   --! Header output
   signal sel_hdr_out          : std_logic_vector(HDR_WIDTH-1 downto 0);

   --! FLU input signals
   signal in_rx_data       : std_logic_vector(INPUTS*DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos    : std_logic_vector(INPUTS*SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos    : std_logic_vector(INPUTS*log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop        : std_logic_vector(INPUTS-1 downto 0);
   signal in_rx_eop        : std_logic_vector(INPUTS-1 downto 0);
   signal in_rx_src_rdy    : std_logic_vector(INPUTS-1 downto 0);
   signal in_rx_dst_rdy_sig   : std_logic_vector(INPUTS-1 downto 0);
   signal rx_sop_used         : std_logic_vector(INPUTS-1 downto 0);
   signal in_rx_dst_rdy    : std_logic_vector(INPUTS-1 downto 0);
   signal in_rx_id         : std_logic_vector(INPUTS*ID_WIDTH-1 downto 0);
   signal in_rx_hdr        : std_logic_vector(INPUTS*HDR_WIDTH-1 downto 0);

   --! FLU bus from FLU multiplexer to FLU PIPE
   constant DATA_JUICE_WIDTH          : integer := DATA_WIDTH+ENABLE_ID*ID_WIDTH+HDR_ENABLE*HDR_WIDTH;

   signal flu_pipe_rx_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flu_pipe_rx_data_id       : std_logic_vector(DATA_JUICE_WIDTH-1 downto 0);
   signal flu_pipe_tx_data_id       : std_logic_vector(DATA_JUICE_WIDTH-1 downto 0);
   signal flu_pipe_rx_sop_pos       : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flu_pipe_rx_eop_pos       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal flu_pipe_rx_eop_pos_id    : std_logic_vector(log2(DATA_JUICE_WIDTH/8)-1 downto 0);
   signal flu_pipe_tx_eop_pos_id    : std_logic_vector(log2(DATA_JUICE_WIDTH/8)-1 downto 0);
   signal flu_pipe_rx_sop           : std_logic;
   signal flu_pipe_rx_eop           : std_logic;
   signal flu_pipe_rx_src_rdy       : std_logic;
   signal flu_pipe_rx_dst_rdy       : std_logic;

   --! Helping signals for the DSP Muxes
   signal ce_en                     : std_logic;

   --! \brief Helping function for conversion of boolean to integer
   function BoolToInt(X : boolean) return integer is
   begin
      if(X = true)then
         return 1;
      end if;

      return 0;
   end function;

   --! Component declaration
   component FLU_MULTIPLEXER_DSP is
      generic(
         DATA_WIDTH    : integer := 512;
         SOP_POS_WIDTH : integer := 3;
         INPUT_PORTS   : integer := 8;
         REG_IN      : integer := 1;
         REG_OUT     : integer := 1;
         REG_LVL     : integer := 1
      );
      port(
         CLK            : in  std_logic;
         RESET          : in  std_logic;
         SEL            : in std_logic_vector(log2(INPUT_PORTS)-1 downto 0);
         SEL_RDY        : in std_logic;
         SEL_NEXT       : out std_logic;
         RX_DATA       : in std_logic_vector(INPUT_PORTS*DATA_WIDTH-1 downto 0);
         RX_SOP_POS    : in std_logic_vector(INPUT_PORTS*SOP_POS_WIDTH-1 downto 0);
         RX_EOP_POS    : in std_logic_vector(INPUT_PORTS*log2(DATA_WIDTH/8)-1 downto 0);
         RX_SOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
         RX_EOP        : in std_logic_vector(INPUT_PORTS-1 downto 0);
         RX_SRC_RDY    : in std_logic_vector(INPUT_PORTS-1 downto 0);
         RX_DST_RDY    : out std_logic_vector(INPUT_PORTS-1 downto 0);
         TX_DATA       : out std_logic_vector(DATA_WIDTH-1 downto 0);
         TX_SOP_POS    : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
         TX_EOP_POS    : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
         TX_SOP        : out std_logic;
         TX_EOP        : out std_logic;
         TX_SRC_RDY    : out std_logic;
         TX_DST_RDY    : in std_logic
      );
   end component;

   component MUX_DSP_GEN is
     generic (
        DATA_WIDTH  : integer := 512;
        MUX_WIDTH   : integer := 8;
        REG_IN      : integer := 1;
        REG_OUT     : integer := 1;
        REG_LVL     : integer := 1
     );
     port (
        CLK      : in  std_logic;
        RESET    : in  std_logic;
        DATA_IN  : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
        CE_IN    : in  std_logic;
        CE_OUT   : in  std_logic;
        CE_LVL   : in std_logic;
        SEL      : in std_logic_vector(log2(MUX_WIDTH)-1 downto 0);
        DATA_OUT : out std_logic_vector(DATA_WIDTH-1 downto 0)
     );
   end component;

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
   RX_DST_RDY        <= in_rx_dst_rdy_sig;
   in_rx_id          <= ID_IN;
   in_rx_hdr         <= RX_HDR;

   --! Generation of booster infrastructure
   FLOW_BOOSTER_GEN:for i in 0 to INPUTS-1 generate
      --! \brief SOP used detector (will be active during
      --! whole transaction)
      sop_trans_detp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               rx_sop_used(i) <= '0';
            else
               if(in_rx_src_rdy(i) = '1' and
                  in_rx_dst_rdy(i) = '1' and in_rx_sop(i) = '1' and in_rx_eop(i) = '0')then
                  --! Sop has been detected
                     rx_sop_used(i) <= '1';
               elsif(in_rx_src_rdy(i) = '1' and
                     in_rx_dst_rdy(i) = '1' and in_rx_eop(i) = '1' and in_rx_sop(i) = '0')then
                  --! Eop has been detected
                     rx_sop_used(i) <= '0';
               end if;
            end if;
         end if;
      end process;

      -- Copy the destinatin ready signal if valid data are prepared.
      -- Two possible situations for dst rdy copy:
      -- 1) Start of transaction is detected
      -- 2) Transaction is running
      --
      -- If the transaction is not running, we assert logic one to take all the data forward
      in_rx_dst_rdy_sig(i) <= in_rx_dst_rdy(i)
                              when((rx_sop_used(i) = '0' and in_rx_sop(i) = '1' and in_rx_src_rdy(i) = '1') or
                                   (rx_sop_used(i) = '1'))
                           else '1';
   end generate;

   --! No DSP multiplexor is generated in this case, therefore use the traditional
   --! implementation of the FLU multiplexor and other generic multiplexors.
   NO_DSP_MUX_GEN:if(ENABLE_DSP = false) generate
      --! FLU multiplexer for selection of Aligned FLU flow
      FLU_MUX_I:entity work.FLU_MULTIPLEXER_PACKET
         generic map(
             DATA_WIDTH       => DATA_WIDTH,
             SOP_POS_WIDTH    => SOP_POS_WIDTH,
             INPUT_PORTS      => INPUTS,
             -- is multiplexer blocking or not
               -- when TRUE:  not selected ports are blocked
               -- when FALSE: not selected ports discard packets at the same rate as selected one forwarding
               --             something like exclusive packet selection
             BLOCKING         => FLU_MUX_BLOCKING
         )
         port map(
             -- Common interface
            RESET          => RESET,
            CLK            => CLK,

            SEL            => flu_mux_sel,
            SEL_READY      => flu_mux_sel_rdy,
            SEL_NEXT       => flu_mux_sel_nxt,

            -- Frame Link Unaligned input interfaces
            RX_DATA       => in_rx_data,
            RX_SOP_POS    => in_rx_sop_pos,
            RX_EOP_POS    => in_rx_eop_pos,
            RX_SOP        => in_rx_sop,
            RX_EOP        => in_rx_eop,
            RX_SRC_RDY    => in_rx_src_rdy,
            RX_DST_RDY    => in_rx_dst_rdy,

            -- Frame Link Unaligned concentrated interface
            TX_DATA       => flu_pipe_rx_data,
            TX_SOP_POS    => flu_pipe_rx_sop_pos,
            TX_EOP_POS    => flu_pipe_rx_eop_pos,
            TX_SOP        => flu_pipe_rx_sop,
            TX_EOP        => flu_pipe_rx_eop,
            TX_SRC_RDY    => flu_pipe_rx_src_rdy,
            TX_DST_RDY    => flu_pipe_rx_dst_rdy
         );

         --! ID MUX
         ID_MUX_I:entity work.GEN_MUX
         generic map(
            DATA_WIDTH  => ID_WIDTH,
            MUX_WIDTH   => INPUTS
         )
         port map(
            DATA_IN     => in_rx_id,
            SEL         => flu_mux_sel,
            DATA_OUT    => sel_id_out
         );

         --! Header mux
         HDR_MUX_I:entity work.GEN_MUX
         generic map(
            DATA_WIDTH  => HDR_WIDTH,
            MUX_WIDTH   => INPUTS
         )
         port map(
            DATA_IN     => in_rx_hdr,
            SEL         => flu_mux_sel,
            DATA_OUT    => sel_hdr_out
         );
      end generate;

      --! DSP multiplexor is generated in this stage. Therefore, generate the DSP multiplexor and
      --! compose the data with header and id.
      DPS_MULTIPLEXOR_GEN:if(ENABLE_DSP = true)generate
         --! Special DSP based multiplexor for FLU
         FLU_DSP_MUX_I: FLU_MULTIPLEXER_DSP
         generic map(
            --! \brief Data width of the Multiplexer
            DATA_WIDTH     => DATA_WIDTH,
            --! \brief Width of the SOP_POS bus
            SOP_POS_WIDTH  => SOP_POS_WIDTH,
            --! \brief Number of input ports
            INPUT_PORTS    => INPUTS,

            --! Input pipeline registers (0, 1)
            REG_IN         => BoolToInt(OUT_PIPE_EN),
            --! Output pipeline registers (0, 1)
            REG_OUT        => BoolToInt(OUT_PIPE_EN),
            --! Pipeline between muxs levels (0, 1)
            REG_LVL        => BoolToInt(OUT_PIPE_EN)
         )
         port map(
            -- --------------------------------------------------
            --! \name Common interface
            -- --------------------------------------------------
            CLK            => CLK,
            RESET          => RESET,

            -- --------------------------------------------------
            --! \name Selection interface
            -- --------------------------------------------------
            --! Select input
            SEL            => flu_mux_sel,
            --! Confirmation of selected input
            SEL_RDY        => flu_mux_sel_rdy,
            --! Ready to get new request
            SEL_NEXT       => flu_mux_sel_nxt,

            -- --------------------------------------------------
            --! \name Frame Link Unaligned input interfaces
            -- --------------------------------------------------
            RX_DATA        => in_rx_data,
            RX_SOP_POS     => in_rx_sop_pos,
            RX_EOP_POS     => in_rx_eop_pos,
            RX_SOP         => in_rx_sop,
            RX_EOP         => in_rx_eop,
            RX_SRC_RDY     => in_rx_src_rdy,
            RX_DST_RDY     => in_rx_dst_rdy,

            -- --------------------------------------------------
            --! \name Frame Link Unaligned concentrated interface
            -- --------------------------------------------------
            TX_DATA        => flu_pipe_rx_data,
            TX_SOP_POS     => flu_pipe_rx_sop_pos,
            TX_EOP_POS     => flu_pipe_rx_eop_pos,
            TX_SOP         => flu_pipe_rx_sop,
            TX_EOP         => flu_pipe_rx_eop,
            TX_SRC_RDY     => flu_pipe_rx_src_rdy,
            TX_DST_RDY     => flu_pipe_rx_dst_rdy
         );

         --! Generation of the CE signal
         ce_en <= flu_pipe_rx_dst_rdy;

         --! Generate the HDR DSP multiplexor
         HDR_MUX_I: MUX_DSP_GEN
         generic map(
            DATA_WIDTH     => HDR_WIDTH,
            MUX_WIDTH      => INPUTS,
            --! Input pipeline registers (0, 1)
            REG_IN         => BoolToInt(OUT_PIPE_EN),
            --! Output pipeline registers (0, 1)
            REG_OUT        => BoolToInt(OUT_PIPE_EN),
            --! Pipeline between muxs levels (0, 1)
            REG_LVL        => BoolToInt(OUT_PIPE_EN)
         )
         port map(
            --! Clock input
            CLK         => CLK,
            --! Reset input
            RESET       => RESET,
            --! Data input
            DATA_IN     => in_rx_hdr,
            --! Clock enable for input pipeline registers
            CE_IN       => ce_en,
            --! Clock enable for output pipeline registers
            CE_OUT      => ce_en,
            --! Clock enable for lvls
            CE_LVL      => ce_en,
            --! Select input data
            SEL         => flu_mux_sel,
            --! output
            DATA_OUT    => sel_hdr_out
         );

         --! Generate the ID DSP multiplexor
         ID_MUX_I: MUX_DSP_GEN
         generic map(
            DATA_WIDTH     => ID_WIDTH,
            MUX_WIDTH      => INPUTS,
            --! Input pipeline registers (0, 1)
            REG_IN         => BoolToInt(OUT_PIPE_EN),
            --! Output pipeline registers (0, 1)
            REG_OUT        => BoolToInt(OUT_PIPE_EN),
            --! Pipeline between muxs levels (0, 1)
            REG_LVL        => BoolToInt(OUT_PIPE_EN)
         )
         port map(
            --! Clock input
            CLK            => CLK,
            --! Reset input
            RESET          => RESET,
            --! Data input
            DATA_IN        => in_rx_id,
            --! Clock enable for input pipeline registers
            CE_IN          => ce_en,
            --! Clock enable for output pipeline registers
            CE_OUT         => ce_en,
            --! Clock enable for lvls
            CE_LVL         => ce_en,
            --! Select input data
            SEL            => flu_mux_sel,
            --! output
            DATA_OUT       => sel_id_out
         );
      end generate;

      -- Input RR selection logic ---------------------------------------------
      --! SOP signal is valid
      next_req_vld <= flu_mux_sel_nxt and flu_mux_sel_rdy;

      -- Implementation of Round Robin selection ----------
      --! Generate request signals
      RR_REQ_GEN:for i in 0 to INPUTS-1 generate
         rr_req(i) <= in_rx_src_rdy(i) and in_rx_sop(i);
      end generate;

      --! Register for storing of last assigned request
      prev_rr_regp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               rr_req_prev <= (others => '0');
            else
               if(next_req_vld = '1')then
                  rr_req_prev <= rr_req_win;
               end if;
            end if;
         end if;
      end process;

      --! Shift previous request
      rr_req_shifted(0) <= '0';
      rr_req_shifted(INPUTS-1 downto 1) <= rr_req_prev(INPUTS-2 downto 0);

      --! Generation of round robin mask
      INTERFACE_POS_GEN:for i in 0 to INPUTS-1 generate
         OR_I:entity work.GEN_OR
            generic map(
               --! \brief Width of input signal, number of bits to OR.
               --! \details Must be greater than 0.
               OR_WIDTH    => i+1
            )
            port map(
               --! Input data, vector of bits to OR.
               DI    => rr_req_shifted(i downto 0),
               --! Output data, result of OR.
               DO    => rr_req_mask(i)
            );
      end generate;

      --! Masked version of actual input request
      rr_req_masked  <= rr_req and rr_req_mask;

         -- Extract LSB bits from masked input
      rr_lsb_req_masked_winp:process(rr_req_masked)
      begin
         rr_lsb_req_masked <= (others=>'0');

         for i in INPUTS-1 downto 0 loop
            if(rr_req_masked(i) = '1')then
               rr_lsb_req_masked <= (others=>'0');
               rr_lsb_req_masked(i) <= '1';
            end if;
         end loop;
      end process;

      -- Extract LSB bits from non-masked input
      rr_lsb_req_winp:process(rr_req)
      begin
         rr_lsb_req <= (others=>'0');

         for i in INPUTS-1 downto 0 loop
            if(rr_req(i) = '1')then
               rr_lsb_req <= (others=>'0');
               rr_lsb_req(i) <= '1';
            end if;
         end loop;
      end process;

         -- Select output (output will be in one hot)
      rr_req_win <= rr_lsb_req_masked when(rr_req_masked /= 0)
                    else rr_lsb_req;

      -- Generation of FLU multiplexer signals --------------------------------
      --! Process for selection of output port
      out_port_genp:process(rr_req_win)
      begin
         --Default signal value
         flu_mux_sel <= (others=>'0');

         for i in 0 to INPUTS-1 loop
            if(rr_req_win(i) = '1')then
               -- Output will be on the possition with logical '1'
               flu_mux_sel <= conv_std_logic_vector(i,log2(INPUTS));
            end if;
         end loop;
      end process;

      --! Generation of selection ready signal (out input is selected when
      flu_mux_sel_rdy <= '1' when (rr_req /= 0)
                         else '0';

      -- ----------------------------------------------------------------------
      -- Ouptput pipeline (depends on generic OUT_PIPE_EN)
      -- ----------------------------------------------------------------------
      --! Pipeline is being generated and
      PIPE_GEN:if(OUT_PIPE_EN = true )generate
         NO_HDR_DATA_ID_GEN:if(HDR_ENABLE = 0 and ENABLE_ID = 1)generate
            --! Map of DATA and ID
            flu_pipe_rx_data_id <= sel_id_out & flu_pipe_rx_data;
         end generate;

         NO_HDR_DATA_NO_ID_GEN:if(HDR_ENABLE = 0 and ENABLE_ID = 0)generate
            --! Map of DATA and ID
            flu_pipe_rx_data_id <= flu_pipe_rx_data;
         end generate;

         HDR_DATA_ID_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 1)generate
            --! Map of DATA,HEADER and ID
            flu_pipe_rx_data_id <= sel_hdr_out & sel_id_out & flu_pipe_rx_data;
         end generate;

         HDR_DATA_NO_ID_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 0)generate
            --! Map of DATA,HEADER and ID
            flu_pipe_rx_data_id <= sel_hdr_out & flu_pipe_rx_data;
         end generate;

         --! EOP_POS ID map (common for both variants)
         eop_pos_id_mapp:process(flu_pipe_rx_eop_pos)
         begin
            flu_pipe_rx_eop_pos_id <= (others=>'0');
            flu_pipe_rx_eop_pos_id(log2(DATA_WIDTH/8)-1 downto 0) <=
               flu_pipe_rx_eop_pos;
         end process;

         --! FLU output pipeline
         OUT_PIPE_I:entity work.FLU_PIPE
            generic map(
               -- FrameLinkUnaligned Data Width
               DATA_WIDTH     => DATA_JUICE_WIDTH,
               SOP_POS_WIDTH  => SOP_POS_WIDTH,
               USE_OUTREG     => FLU_PIPE_USE_OUTREG,
               FAKE_PIPE      => FLU_PIPE_FAKE_PIPE
            )
            port map(
               -- Common interface
               CLK            => CLK,
               RESET          => RESET,

               -- Input interface
               RX_DATA        => flu_pipe_rx_data_id,
               RX_SOP_POS     => flu_pipe_rx_sop_pos,
               RX_EOP_POS     => flu_pipe_rx_eop_pos_id,
               RX_SOP         => flu_pipe_rx_sop,
               RX_EOP         => flu_pipe_rx_eop,
               RX_SRC_RDY     => flu_pipe_rx_src_rdy,
               RX_DST_RDY     => flu_pipe_rx_dst_rdy,

               -- Output interface
               TX_DATA        => flu_pipe_tx_data_id,
               TX_SOP_POS     => TX_SOP_POS,
               TX_EOP_POS     => flu_pipe_tx_eop_pos_id,
               TX_SOP         => TX_SOP,
               TX_EOP         => TX_EOP,
               TX_SRC_RDY     => TX_SRC_RDY,
               TX_DST_RDY     => TX_DST_RDY,

               -- Debuging interface ---------------------------------------------------
               DEBUG_BLOCK       => '0',
               DEBUG_DROP        => '0',
               DEBUG_SRC_RDY     => open,
               DEBUG_DST_RDY     => open,
               DEBUG_SOP         => open,
               DEBUG_EOP         => open
            );

            --! Correction of output data
         ID_OUT_GEN:if(ENABLE_ID = 1)generate
            ID_OUT <= flu_pipe_tx_data_id(DATA_WIDTH+ID_WIDTH-1 downto DATA_WIDTH);
         end generate;

            TX_DATA <= flu_pipe_tx_data_id(DATA_WIDTH-1 downto 0);
            TX_EOP_POS <= flu_pipe_tx_eop_pos_id(log2(DATA_WIDTH/8)-1 downto 0);

            NO_HDR_OUT_GEN:if(HDR_ENABLE = 0)generate
               TX_HDR <= (others=>'0');
            end generate;

            HDR_ID_OUT_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 1)generate
               TX_HDR <=
               flu_pipe_tx_data_id(DATA_WIDTH+ID_WIDTH+HDR_WIDTH-1 downto ID_WIDTH+DATA_WIDTH);
            end generate;

            HDR_NO_ID_OUT_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 0)generate
               TX_HDR <=
               flu_pipe_tx_data_id(DATA_WIDTH+HDR_WIDTH-1 downto DATA_WIDTH);
            end generate;
      end generate;


      --! No pipeline is being generated
      NO_PIPE_GEN:if(OUT_PIPE_EN = false )generate
         --! Connect output from FLU multiplexer directly to output
         TX_DATA              <= flu_pipe_rx_data;
         TX_SOP_POS           <= flu_pipe_rx_sop_pos;
         TX_EOP_POS           <= flu_pipe_rx_eop_pos;
         TX_SOP               <= flu_pipe_rx_sop;
         TX_EOP               <= flu_pipe_rx_eop;
         TX_SRC_RDY           <= flu_pipe_rx_src_rdy;
         flu_pipe_rx_dst_rdy  <= TX_DST_RDY;

         NO_ID_NO_PIPE:if(ENABLE_ID = 1)generate
            ID_OUT <= sel_id_out;
         end generate;

         NO_HDR_OUT_GEN:if(HDR_ENABLE = 0)generate
            TX_HDR <= (others=>'0');
         end generate;

         HDR_OUT_GEN:if(HDR_ENABLE = 1)generate
            TX_HDR <= sel_hdr_out;
         end generate;
      end generate;

end architecture;
