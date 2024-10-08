--
-- align_arch.vhd: FLU align component architecture
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
architecture FULL of FLUA_BINDER is
   -- Generation of lookup table with shift values ----------------------------
   --! Lookup table with shifting values
   type t_mem_lookup is array (0 to 2**SOP_POS_WIDTH-1) of
      std_logic_vector(SOP_POS_WIDTH-1 downto 0);

   --! Lookup table with shiftig values
   type t_mem_lookup_gap is array (0 to 2**SOP_POS_WIDTH-1) of
      std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   --! Lookup table with shiftig bit information
   type t_mem_lookup_null_shift is array (0 to 2**SOP_POS_WIDTH-1) of
      std_logic;

   --! Function for generation of shifter lookup table
   function generateLookupTable(sop_width : in integer) return t_mem_lookup is

      -- Local variables
      variable mem_ret  : t_mem_lookup;
   begin
      --Setup default values
      ZERO_LOOP:for i in 0 to 2**sop_width-1 loop
         mem_ret(i) := (others=>'0');
      end loop;

      --Setup new shifting values
      SHIFT_LOOP:for i in 0 to 2**sop_width-2 loop
         mem_ret(i) :=  conv_std_logic_vector(i+1,sop_width);
      end loop;

      mem_ret(2**sop_width-1) := (others=>'0');

      return mem_ret;
   end function;

   --! Function for generation of shifter lookup table with gap reservation
   function generateLookupTableWithGap(sop_width : in integer) return t_mem_lookup_gap is
      -- Local variable
      variable mem_ret : t_mem_lookup_gap;
   begin
      --Setup new shifting values (reserve 128 bit for header)
      SHIFT_LOOP:for i in 0 to 2**sop_width-1 loop
         mem_ret(i) := conv_std_logic_vector(
               i + (128 / (DATA_WIDTH/(2**sop_width))) + 1 mod 2**sop_width,
               sop_width);
      end loop;

      return mem_ret;
   end function;

   function generateNotNullShiftLookup(table : in t_mem_lookup_gap;sop_width : in integer)
      return t_mem_lookup_null_shift is

      variable retMem : t_mem_lookup_null_shift;
   begin
      for i in 0 to 2**sop_width-1 loop
         if(table(i) = 0)then
            -- Shifting value equals to 0
            retMem(i) := '0';
         else
            -- Shifting value differs from 0
            retMem(i) := '1';
         end if;
      end loop;

      return retMem;
   end function;

   --! Constant array declaration with new shifting values(this is needed
   constant shift_lookup_mem0  : t_mem_lookup := generateLookupTable(SOP_POS_WIDTH);
   constant shift_lookup_mem1  : t_mem_lookup := generateLookupTable(SOP_POS_WIDTH);

   constant shift_lookup_gap_mem0 : t_mem_lookup_gap := generateLookupTableWithGap(SOP_POS_WIDTH);
   constant shift_lookup_gap_mem1 : t_mem_lookup_gap := generateLookupTableWithGap(SOP_POS_WIDTH);

   constant shift_lookup_null_gap_mem0 : t_mem_lookup_null_shift :=
      generateNotNullShiftLookup(shift_lookup_gap_mem0,SOP_POS_WIDTH);
   constant shift_lookup_null_gap_mem1 : t_mem_lookup_null_shift :=
      generateNotNullShiftLookup(shift_lookup_gap_mem1,SOP_POS_WIDTH);

   --! Delay registers for the shift value
   signal reg_flua_shift0           : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal reg_flua_not_null_shift0  : std_logic;
   signal reg_flua_shift0_en  : std_logic;
   signal reg_flua_shift0_clr : std_logic;
   signal reg_flua_shift1              : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal reg_flua_not_null_shift1     : std_logic;
   signal reg_flua_shift1_en  : std_logic;
   signal reg_flua_shift1_clr : std_logic;

   -- Constants and ranges declarations
   --! EOP_POS bus length
   constant EOP_POS_BUS_WIDTH    : integer := log2(DATA_WIDTH/8);
   --! EOP block range declaration
   subtype EOP_BLK is natural range EOP_POS_BUS_WIDTH-1 downto EOP_POS_BUS_WIDTH-SOP_POS_WIDTH;
   --! Number of blocks in word
   constant BLK_COUNT   : integer := 2**SOP_POS_WIDTH;
   --! Width of one block
   constant BLK_WIDTH   : integer := DATA_WIDTH/BLK_COUNT;

   -- Signals declaration -----------------------------------------------------
   --! FLU inpiut signals
      -- Lane 0
   signal in_rx_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos0   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos0   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop0       : std_logic;
   signal in_rx_eop0       : std_logic;
   signal in_rx_src_rdy0   : std_logic;
   signal in_rx_dst_rdy0   : std_logic;
   signal in_rx_id0        : std_logic_vector(ID_WIDTH-1 downto 0);
   signal in_rx_hdr_data0  : std_logic_vector(HDR_WIDTH-1 downto 0);

      -- Lane 1
   signal in_rx_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_rx_sop_pos1   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal in_rx_eop_pos1   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal in_rx_sop1       : std_logic;
   signal in_rx_eop1       : std_logic;
   signal in_rx_src_rdy1   : std_logic;
   signal in_rx_dst_rdy1   : std_logic;
   signal in_rx_id1        : std_logic_vector(ID_WIDTH-1 downto 0);
   signal in_rx_hdr_data1  : std_logic_vector(HDR_WIDTH-1 downto 0);

   --! Output from shifting units
      -- Lane 0
   signal flua_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flua_sop_pos0   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flua_eop_pos0   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal flua_sop0       : std_logic;
   signal flua_eop0       : std_logic;
   signal flua_src_rdy0   : std_logic;
   signal flua_dst_rdy0   : std_logic;
   signal flua_id0        : std_logic_vector(ID_WIDTH-1 downto 0);
   signal flua_hdr0       : std_logic_vector(HDR_WIDTH-1 downto 0);

      -- Lane 1
   signal flua_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal flua_sop_pos1   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flua_eop_pos1   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal flua_sop1       : std_logic;
   signal flua_eop1       : std_logic;
   signal flua_src_rdy1   : std_logic;
   signal flua_dst_rdy1   : std_logic;
   signal flua_id1        : std_logic_vector(ID_WIDTH-1 downto 0);
   signal flua_hdr1       : std_logic_vector(HDR_WIDTH-1 downto 0);

   --! Shifting information
   signal flua_shift0_vld     : std_logic;
   signal flua_shift1_vld     : std_logic;
   signal flua_shift0_vld_gap : std_logic_vector(1 downto 0);
   signal flua_shift1_vld_gap : std_logic_vector(1 downto 0);

   signal flua_shift0      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal flua_shift1      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);

   --! Signal for the output line activation
   signal act_lane0        : std_logic;
   signal act_lane1        : std_logic;

   --! Signals for EOP masking
   signal mask_eop0        : std_logic;
   signal mask_eop1        : std_logic;

   --! Information about shifting
   signal not_null_shift0  : std_logic;
   signal not_null_shift1  : std_logic;

   --! Pipeline register signals
      --! Port 0
   signal reg_flua_data0         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_flua_sop0          : std_logic;
   signal reg_flua_eop0          : std_logic;
   signal reg_flua_sop_pos0      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal reg_flua_eop_pos0      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal reg_flua_src_rdy0      : std_logic;
   signal reg_flua_id0           : std_logic_vector(ID_WIDTH-1 downto 0);
   signal reg_flua_hdr0          : std_logic_vector(HDR_WIDTH-1 downto 0);

      --! Port 1
   signal reg_flua_data1         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_flua_sop1          : std_logic;
   signal reg_flua_eop1          : std_logic;
   signal reg_flua_sop_pos1      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal reg_flua_eop_pos1      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal reg_flua_src_rdy1      : std_logic;
   signal reg_flua_id1           : std_logic_vector(ID_WIDTH-1 downto 0);
   signal reg_flua_hdr1          : std_logic_vector(HDR_WIDTH-1 downto 0);

      --! Masked data
   signal masked_flua_data0      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal masked_flua_data1      : std_logic_vector(DATA_WIDTH-1 downto 0);

      --! Control signals
   signal reg_act_lane0          : std_logic;
   signal reg_act_lane1          : std_logic;

   --! FLU output signals + computation of required data width
   constant FLU_PIPE_WIDTH    : integer := DATA_WIDTH+ENABLE_ID*ID_WIDTH+HDR_ENABLE*HDR_WIDTH;

   signal out_tx_data         : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal out_tx_data_id      : std_logic_vector(FLU_PIPE_WIDTH-1 downto 0);
   signal out_tx_data_id_out  : std_logic_vector(FLU_PIPE_WIDTH-1 downto 0);
   signal out_tx_sop_pos      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal out_tx_eop_pos      : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal out_tx_eop_pos_id      : std_logic_vector(log2((FLU_PIPE_WIDTH)/8)-1 downto 0);
   signal out_tx_eop_pos_id_out  : std_logic_vector(log2((FLU_PIPE_WIDTH)/8)-1 downto 0);
   signal out_tx_sop          : std_logic;
   signal out_tx_eop          : std_logic;
   signal out_tx_src_rdy      : std_logic;
   signal out_tx_dst_rdy      : std_logic;
   signal out_tx_id           : std_logic_vector(ID_WIDTH-1 downto 0);
   signal out_tx_hdr          : std_logic_vector(HDR_WIDTH-1 downto 0);

begin

   -- -------------------------------------------------------------------------
   -- Input port map
   -- -------------------------------------------------------------------------
   -- Deal with map of the input RX flow
   in_rx_data0       <= RX_DATA0;
   in_rx_sop_pos0    <= RX_SOP_POS0;
   in_rx_eop_pos0    <= RX_EOP_POS0;
   in_rx_sop0        <= RX_SOP0;
   in_rx_eop0        <= RX_EOP0;
   in_rx_src_rdy0    <= RX_SRC_RDY0;
   RX_DST_RDY0       <= in_rx_dst_rdy0;
   in_rx_id0         <= ID0;
   in_rx_hdr_data0   <= RX_HDR_DATA0;

   in_rx_data1       <= RX_DATA1;
   in_rx_sop_pos1    <= RX_SOP_POS1;
   in_rx_eop_pos1    <= RX_EOP_POS1;
   in_rx_sop1        <= RX_SOP1;
   in_rx_eop1        <= RX_EOP1;
   in_rx_src_rdy1    <= RX_SRC_RDY1;
   RX_DST_RDY1       <= in_rx_dst_rdy1;
   in_rx_id1         <= ID1;
   in_rx_hdr_data1   <= RX_HDR_DATA1;

   -- -------------------------------------------------------------------------
   -- FLUA Shifters
   -- -------------------------------------------------------------------------
   --! FLUA Shifter Lane 0
   FLUA_SHIFTER_0_I:entity work.FLUA_SHIFTER
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         ID_WIDTH       => ID_WIDTH,
         ENABLE_ID      => ENABLE_ID,

         --! Header configuration
         HDR_ENABLE     => HDR_ENABLE,
         HDR_WIDTH      => HDR_WIDTH,

         --! Changes for binding with FLU gap,
         --! if short frame with non zero shift is detected,
         --! ignore first EOP because it is not valid, this signal
         --! not masked to reach better frequency.
         FLU_GAP_EN     => RESERVE_GAP_EN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Control interface
         -- --------------------------------------------------
         -- Shifting value of SOP_POS; this signal is valid
         -- when RX_SOP is asserted.
         SHIFT_VAL      => flua_shift0,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA        => in_rx_data0,
         RX_SOP_POS     => in_rx_sop_pos0,
         RX_EOP_POS     => in_rx_eop_pos0,
         RX_SOP         => in_rx_sop0,
         RX_EOP         => in_rx_eop0,
         RX_SRC_RDY     => in_rx_src_rdy0,
         RX_DST_RDY     => in_rx_dst_rdy0,
         ID_IN          => in_rx_id0,
         HDR_IN         => in_rx_hdr_data0,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_DATA        => flua_data0,
         TX_SOP_POS     => flua_sop_pos0,
         TX_EOP_POS     => flua_eop_pos0,
         TX_SOP         => flua_sop0,
         TX_EOP         => flua_eop0,
         TX_SRC_RDY     => flua_src_rdy0,
         TX_DST_RDY     => flua_dst_rdy0,
         ID_OUT         => flua_id0,
         HDR_OUT        => flua_hdr0
      );

   --! FLUA Shifter Lane 1
   FLUA_SHIFTER_1_I:entity work.FLUA_SHIFTER
      generic map(
         -- FLU Config -----------------------------
         --! FLU protocol generics
         DATA_WIDTH     => DATA_WIDTH,
         SOP_POS_WIDTH  => SOP_POS_WIDTH,
         ID_WIDTH       => ID_WIDTH,
         ENABLE_ID      => ENABLE_ID,

         --! Header configuration
         HDR_ENABLE     => HDR_ENABLE,
         HDR_WIDTH      => HDR_WIDTH,

         --! Changes for binding with FLU gap,
         --! if short frame with non zero shift is detected,
         --! ignore first EOP because it is not valid, this signal
         --! not masked to reach better frequency.
         FLU_GAP_EN     => RESERVE_GAP_EN
      )
      port map(
          -- -------------------------------------------------
          -- \name Common interface
          -- -------------------------------------------------
         RESET          => RESET,
         CLK            => CLK,

         -- --------------------------------------------------
         -- \name Control interface
         -- --------------------------------------------------
         -- Shifting value of SOP_POS; this signal is valid
         -- when RX_SOP is asserted.
         SHIFT_VAL      => flua_shift1,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned input interface
         -- --------------------------------------------------
         RX_DATA        => in_rx_data1,
         RX_SOP_POS     => in_rx_sop_pos1,
         RX_EOP_POS     => in_rx_eop_pos1,
         RX_SOP         => in_rx_sop1,
         RX_EOP         => in_rx_eop1,
         RX_SRC_RDY     => in_rx_src_rdy1,
         RX_DST_RDY     => in_rx_dst_rdy1,
         ID_IN          => in_rx_id1,
         HDR_IN         => in_rx_hdr_data1,

         -- --------------------------------------------------
         -- \name Frame Link Unaligned output interface
         -- --------------------------------------------------
         TX_DATA        => flua_data1,
         TX_SOP_POS     => flua_sop_pos1,
         TX_EOP_POS     => flua_eop_pos1,
         TX_SOP         => flua_sop1,
         TX_EOP         => flua_eop1,
         TX_SRC_RDY     => flua_src_rdy1,
         TX_DST_RDY     => flua_dst_rdy1,
         ID_OUT         => flua_id1,
         HDR_OUT        => flua_hdr1
      );

   -- -------------------------------------------------------------------------
   -- Binding control logic
   -- -------------------------------------------------------------------------
   NO_GAP_RESERVE_GEN:if(RESERVE_GAP_EN = false)generate
      --! FLUA binder logic
      FLUA_BINDER_FSM_I:entity work.FLUA_BINDER_FSM
         generic map(
            --! FLUA Generics (needed in control FSM)
            SOP_POS_WIDTH  => SOP_POS_WIDTH
         )
         port map(
             -- -------------------------------------------------
             -- \name Common interface
             -- -------------------------------------------------
            RESET          => RESET,
            CLK            => CLK,

            -- --------------------------------------------------
            -- \name FSM inputs
            -- --------------------------------------------------
            --! SOP signals from input lanes 0 and 1
            SOP0           => flua_sop0,
            SRC_RDY0       => flua_src_rdy0,
            SOP1           => flua_sop1,
            SRC_RDY1       => flua_src_rdy1,

            --! Destination ready singal
            DST_RDY        => out_tx_dst_rdy,

            --! EOP* signals from Lane 0
            EOP0           => flua_eop0,
            EOP_POS_BLK0   => flua_eop_pos0(EOP_BLK),

            --! EOP* Signals from Lane 1
            EOP1           => flua_eop1,
            EOP_POS_BLK1   => flua_eop_pos1(EOP_BLK),

            -- --------------------------------------------------
            -- \name FSM outputs
            -- --------------------------------------------------
            --! Output Shifting Information for Lane 0 and 1
            SHIFT0         => flua_shift0_vld,
            SHIFT1         => flua_shift1_vld,

            --! Ouput Line activity
            ACT_LANE0      => act_lane0,
            ACT_LANE1      => act_lane1,

            --! Destination ready signals
            DST_RDY0       => flua_dst_rdy0,
            DST_RDY1       => flua_dst_rdy1
         );

         --! Shift lookup
         flua_shift0 <= shift_lookup_mem0(conv_integer(flua_eop_pos1(EOP_BLK))) when (flua_shift0_vld = '1')
                        else (others=>'0');

         flua_shift1 <= shift_lookup_mem1(conv_integer(flua_eop_pos0(EOP_BLK))) when (flua_shift1_vld = '1')
                        else (others=>'0');

         --! Default signals for EOP masking
         mask_eop0 <= '1';
         mask_eop1 <= '1';
      end generate;

      GAP_RESERVE_GEN:if(RESERVE_GAP_EN = true)generate
         --! Optimized version of the control FSM with gap reservation
         GAP_FSM_I:entity work.FLUA_BINDER_GAP_FSM
            generic map(
               --! FLUA Generics (needed in control FSM)
               SOP_POS_WIDTH     => SOP_POS_WIDTH,
               DATA_WIDTH        => DATA_WIDTH
            )
            port map(
                -- -------------------------------------------------
                -- \name Common interface
                -- -------------------------------------------------
               RESET          => RESET,
               CLK            => CLK,

               -- --------------------------------------------------
               -- \name FSM inputs
               -- --------------------------------------------------
               --! SOP signals from input lanes 0 and 1
               SOP0              => flua_sop0,
               SRC_RDY0          => flua_src_rdy0,
               NOT_NULL_SHIFT0   => not_null_shift0,
               SOP1              => flua_sop1,
               SRC_RDY1          => flua_src_rdy1,
               NOT_NULL_SHIFT1   => not_null_shift1,

               --! Destination ready singal
               DST_RDY        => out_tx_dst_rdy,

               --! EOP* signals from Lane 0
               EOP0           => flua_eop0,
               EOP_POS_BLK0   => flua_eop_pos0(EOP_BLK),

               --! EOP* Signals from Lane 1
               EOP1           => flua_eop1,
               EOP_POS_BLK1   => flua_eop_pos1(EOP_BLK),

               -- --------------------------------------------------
               -- \name FSM outputs
               -- --------------------------------------------------
               --! Output Shifting Information for Lane 0 and 1
               --!   00 - inzert zeros (no shift)
               --!   01 - select live data shift
               --!   10 - select shift from the delay register
               SHIFT0         => flua_shift0_vld_gap,
               SHIFT1         => flua_shift1_vld_gap,

               --! Enable signals for write enable into the register
               SHIFT0_REG_EN  => reg_flua_shift0_en,
               SHIFT0_CLR_REG => reg_flua_shift0_clr,
               SHIFT1_REG_EN  => reg_flua_shift1_en,
               SHIFT1_CLR_REG => reg_flua_shift1_clr,

               --! EOP masking signals
               MASK_EOP0      => mask_eop0,
               MASK_EOP1      => mask_eop1,

               --! Ouput Line activity
               ACT_LANE0      => act_lane0,
               ACT_LANE1      => act_lane1,

               --! Destination ready signals
               DST_RDY0       => flua_dst_rdy0,
               DST_RDY1       => flua_dst_rdy1
            );

         --! \brief Delay register - lane 0 shift value
         flua_shift0_regp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(RESET = '1' or reg_flua_shift0_clr = '1')then
                  reg_flua_shift0 <= (others=>'0');
                  reg_flua_not_null_shift0 <= '0';
               else
                  if(reg_flua_shift0_en = '1' and
                     flua_src_rdy0 = '1' and flua_eop0 = '1' and act_lane0 = '1' )then
                     reg_flua_shift0 <=
                        shift_lookup_gap_mem0(conv_integer(flua_eop_pos0(EOP_BLK)));
                     reg_flua_not_null_shift0 <=
                        shift_lookup_null_gap_mem0(conv_integer(flua_eop_pos0(EOP_BLK)));
                  elsif(reg_flua_shift1_en = '1' and
                     flua_src_rdy1 = '1' and flua_eop1 = '1' and act_lane1 = '1')then
                     reg_flua_shift0 <=
                        shift_lookup_gap_mem1(conv_integer(flua_eop_pos1(EOP_BLK)));
                     reg_flua_not_null_shift0 <=
                        shift_lookup_null_gap_mem1(conv_integer(flua_eop_pos1(EOP_BLK)));
                  end if;
               end if;
            end if;
         end process;

         --! \brief Delay register - lane 1 shift value
         flua_shift1_regp:process(CLK)
         begin
            if(CLK = '1' and CLK'event)then
               if(RESET = '1' or reg_flua_shift1_clr = '1')then
                  reg_flua_shift1 <= (others=>'0');
                  reg_flua_not_null_shift1 <= '0';
               else
                  if(reg_flua_shift0_en = '1' and
                     flua_src_rdy0 = '1' and flua_eop0 = '1' and act_lane0 = '1' )then
                     reg_flua_shift1 <=
                        shift_lookup_gap_mem0(conv_integer(flua_eop_pos0(EOP_BLK)));
                     reg_flua_not_null_shift1 <=
                        shift_lookup_null_gap_mem0(conv_integer(flua_eop_pos0(EOP_BLK)));
                  elsif(reg_flua_shift1_en = '1' and
                     flua_src_rdy1 = '1' and flua_eop1 = '1' and act_lane1 = '1')then
                     reg_flua_shift1 <=
                        shift_lookup_gap_mem1(conv_integer(flua_eop_pos1(EOP_BLK)));
                     reg_flua_not_null_shift1 <=
                        shift_lookup_null_gap_mem1(conv_integer(flua_eop_pos1(EOP_BLK)));
                  end if;
               end if;
            end if;
         end process;

         --! Shift lookup
         flua_shift0 <= shift_lookup_gap_mem0(conv_integer(flua_eop_pos1(EOP_BLK))) when(flua_shift0_vld_gap = "01") else
                        reg_flua_shift0 when (flua_shift0_vld_gap = "10") else
                        (others=>'0');

         flua_shift1 <= shift_lookup_gap_mem1(conv_integer(flua_eop_pos0(EOP_BLK))) when(flua_shift1_vld_gap = "01") else
                        reg_flua_shift1 when (flua_shift1_vld_gap = "10") else
                        (others=>'0');

         --! Generation of not null shift signal
         not_null_shift0 <=
            shift_lookup_null_gap_mem0(conv_integer(flua_eop_pos1(EOP_BLK))) when(flua_shift0_vld_gap = "01") else
            reg_flua_not_null_shift0 when (flua_shift0_vld_gap = "10") else
            '0';

         not_null_shift1 <=
            shift_lookup_null_gap_mem1(conv_integer(flua_eop_pos0(EOP_BLK))) when(flua_shift1_vld_gap = "01") else
            reg_flua_not_null_shift1 when (flua_shift1_vld_gap = "10") else
            '0';

      end generate;

   -- -------------------------------------------------------------------------
   -- Performance registers :-)
   -- -------------------------------------------------------------------------
   --! \brief Just registers, registers and registers
   tune_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            reg_act_lane0 <= '0';
            reg_act_lane1 <= '0';
            reg_flua_sop0 <= '0';
            reg_flua_sop1 <= '0';
            reg_flua_eop0 <= '0';
            reg_flua_eop1 <= '0';
            reg_flua_src_rdy0 <= '0';
            reg_flua_src_rdy1 <= '0';
         else
            if(out_tx_dst_rdy = '1')then
               -- Enable shifting if and only if the destination is ready
                  -- Port 0
               reg_flua_sop_pos0 <= flua_sop_pos0;
               reg_flua_eop_pos0 <= flua_eop_pos0;
               reg_flua_sop0 <= flua_sop0;
               reg_flua_eop0 <= flua_eop0 and mask_eop0;
               reg_flua_src_rdy0 <= flua_src_rdy0;
               reg_act_lane0 <= act_lane0;

                  -- Port 1
               reg_flua_sop_pos1 <= flua_sop_pos1;
               reg_flua_eop_pos1 <= flua_eop_pos1;
               reg_flua_sop1 <= flua_sop1;
               reg_flua_eop1 <= flua_eop1 and mask_eop1;
               reg_flua_src_rdy1 <= flua_src_rdy1;
               reg_act_lane1 <= act_lane1;
            end if;
         end if;

         if(out_tx_dst_rdy = '1')then
            reg_flua_data0 <= flua_data0;
            reg_flua_hdr0 <= flua_hdr0;

            reg_flua_data1 <= flua_data1;
            reg_flua_hdr1 <= flua_hdr1;
         end if;
      end if;
   end process;

ID_TUNE_REG_GEN:if(ENABLE_ID = 1)generate
   tune_id_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(out_tx_dst_rdy = '1')then
            -- Enable shifting if and only if the destination is ready
               -- Port 0 and 1
            reg_flua_id0 <= flua_id0;
            reg_flua_id1 <= flua_id1;
         end if;
      end if;
   end process;
end generate;


   -- Masking of output data (insert zeros after EOP block)
   --! Prepare data
   DATA_BUS_MASK_GENP:for i in 0 to BLK_COUNT-1 generate
      masked_flua_data0((i+1)*BLK_WIDTH-1 downto i*BLK_WIDTH) <=
      (others=>'0') when
         (conv_std_logic_vector(i,SOP_POS_WIDTH) > reg_flua_eop_pos0(EOP_BLK) and
          reg_flua_src_rdy0 = '1' and reg_flua_eop0 = '1')
      else reg_flua_data0((i+1)*BLK_WIDTH-1 downto i*BLK_WIDTH);

      masked_flua_data1((i+1)*BLK_WIDTH-1 downto i*BLK_WIDTH) <=
      (others=>'0') when
         (conv_std_logic_vector(i,SOP_POS_WIDTH) > reg_flua_eop_pos1(EOP_BLK) and
          reg_flua_src_rdy1 = '1' and reg_flua_eop1 = '1')
      else reg_flua_data1((i+1)*BLK_WIDTH-1 downto i*BLK_WIDTH);
   end generate;

   -- -------------------------------------------------------------------------
   -- Generation of FLU output data
   -- -------------------------------------------------------------------------
   --! Generation of output data bus
   out_tx_data <= masked_flua_data0 when(reg_act_lane0 = '1' and reg_act_lane1 = '0') else
                  masked_flua_data1 when(reg_act_lane0 = '0' and reg_act_lane1 = '1') else
                  masked_flua_data0 or masked_flua_data1;

   --! Generation of SOP and SOP_POS signals
   out_tx_sop <= reg_flua_sop0 when(reg_act_lane0 = '1' and reg_flua_sop0 = '1') else
                 reg_flua_sop1 when(reg_act_lane1 = '1' and reg_flua_sop1 = '1')
              else '0';

   out_tx_sop_pos <= reg_flua_sop_pos0 when(reg_act_lane0 = '1' and reg_flua_sop0 = '1') else
                     reg_flua_sop_pos1 when(reg_act_lane1 = '1' and reg_flua_sop1 = '1')
                  else (others=>'0');

   --! Generation of EOP and EOP_POS signals
   out_tx_eop <= reg_flua_eop0 when(reg_act_lane0 = '1' and reg_flua_eop0 = '1') else
                 reg_flua_eop1 when(reg_act_lane1 = '1' and reg_flua_eop1 = '1')
               else '0';

   out_tx_eop_pos <= reg_flua_eop_pos0 when(reg_act_lane0 = '1' and reg_flua_eop0 = '1') else
                     reg_flua_eop_pos1 when(reg_act_lane1 = '1' and reg_flua_eop1 = '1')
               else (others=>'0');

   --! Generation of source ready signals
   out_tx_src_rdy <= reg_flua_src_rdy0 when(reg_act_lane0 = '1' and reg_act_lane1 = '0') else
                  reg_flua_src_rdy1 when(reg_act_lane0 = '0' and reg_act_lane1 = '1') else
                  reg_flua_src_rdy0 or reg_flua_src_rdy1 when(reg_act_lane0 = '1' and reg_act_lane1 = '1')
               else '0';

   --! Generation of ID signal
   out_tx_id <= reg_flua_id0 when(reg_act_lane0 = '1' and reg_flua_sop0 = '1') else
                reg_flua_id1;

   --! Generatoin of output header
   out_tx_hdr <= reg_flua_hdr0 when (reg_act_lane0 = '1' and reg_flua_sop0 = '1') else
                 reg_flua_hdr1;

   -- -------------------------------------------------------------------------
   -- Output port map
   -- -------------------------------------------------------------------------
   GEN_PIPE_EN:if(OUT_PIPE_EN = true)generate
      NO_HDR_DATA_ID_GEN:if(HDR_ENABLE = 0 and ENABLE_ID = 1)generate
         --! Map of DATA and ID
         out_tx_data_id <= out_tx_id & out_tx_data;
      end generate;

      NO_HDR_DATA_NO_ID_GEN:if(HDR_ENABLE = 0 and ENABLE_ID = 0)generate
         --! Map of DATA
         out_tx_data_id <= out_tx_data;
      end generate;

      HDR_DATA_ID_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 1)generate
         --! Map of DATA,Header and ID
         out_tx_data_id <= out_tx_hdr & out_tx_id & out_tx_data;
      end generate;

      HDR_DATA_NO_ID_GEN:if(HDR_ENABLE = 1 and ENABLE_ID = 0)generate
         --! Map of DATA,Header and ID
         out_tx_data_id <= out_tx_hdr & out_tx_data;
      end generate;

      --! EOP_POS ID map
      eop_pos_id_mapp:process(out_tx_eop_pos)
      begin
         out_tx_eop_pos_id <= (others=>'0');
         out_tx_eop_pos_id(log2(DATA_WIDTH/8)-1 downto 0) <=
           out_tx_eop_pos;
      end process;

      --! FLU output pipeline
      OUT_PIPE_I:entity work.FLU_PIPE
         generic map(
            -- FrameLinkUnaligned Data Width
            DATA_WIDTH     => FLU_PIPE_WIDTH,
            SOP_POS_WIDTH  => SOP_POS_WIDTH,
            USE_OUTREG     => OUT_PIPE_OUTREG,
            FAKE_PIPE      => false
         )
         port map(
            -- Common interface
            CLK            => CLK,
            RESET          => RESET,

            -- Input interface
            RX_DATA        => out_tx_data_id,
            RX_SOP_POS     => out_tx_sop_pos,
            RX_EOP_POS     => out_tx_eop_pos_id,
            RX_SOP         => out_tx_sop,
            RX_EOP         => out_tx_eop,
            RX_SRC_RDY     => out_tx_src_rdy,
            RX_DST_RDY     => out_tx_dst_rdy,

            -- Output interface
            TX_DATA        => out_tx_data_id_out,
            TX_SOP_POS     => TX_SOP_POS,
            TX_EOP_POS     => out_tx_eop_pos_id_out,
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
   ID_GEN:if(ENABLE_ID = 1) generate
      ID <= out_tx_data_id_out(DATA_WIDTH+ID_WIDTH-1 downto DATA_WIDTH);
   end generate;

      TX_DATA <= out_tx_data_id_out(DATA_WIDTH-1 downto 0);
      TX_EOP_POS <= out_tx_eop_pos_id_out(log2(DATA_WIDTH/8)-1 downto 0);

      NO_HDR_GEN:if(HDR_ENABLE = 0)generate
         TX_HDR_DATA <= (others=>'0');
      end generate;

      HDR_GEN_ID_EN:if(HDR_ENABLE = 1 and ENABLE_ID = 1)generate
         TX_HDR_DATA <=
         out_tx_data_id_out(DATA_WIDTH+ID_WIDTH+HDR_WIDTH-1 downto ID_WIDTH+DATA_WIDTH);
      end generate;

      HDR_GEN_NO_ID_EN:if(HDR_ENABLE = 1 and ENABLE_ID = 0)generate
         TX_HDR_DATA <=
         out_tx_data_id_out(DATA_WIDTH+HDR_WIDTH-1 downto DATA_WIDTH);
      end generate;
   end generate;

   NO_PIPE_GEN:if(OUT_PIPE_EN = false)generate
      --! FrameLink Unaligned output lane 0
      TX_HDR_DATA          <= out_tx_hdr;
      TX_DATA              <= out_tx_data;
      TX_SOP_POS           <= out_tx_sop_pos;
      TX_EOP_POS           <= out_tx_eop_pos;
      TX_SOP               <= out_tx_sop;
      TX_EOP               <= out_tx_eop;
      TX_SRC_RDY           <= out_tx_src_rdy;
      out_tx_dst_rdy       <= TX_DST_RDY;

      ID_NO_PIPE_GEN:if(ENABLE_ID = 1)generate
         ID                <= out_tx_id;
      end generate;
   end generate;

end architecture FULL;
