--
-- align_ent.vhd: FLU align component
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
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLUA_BINDER_GAP_FSM is
   generic(
      --! FLUA Generics (needed in control FSM)
      SOP_POS_WIDTH  : integer := 2;
      DATA_WIDTH     : integer := 256
   );
   port(
       -- -------------------------------------------------
       -- \name Common interface
       -- -------------------------------------------------
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- --------------------------------------------------
      -- \name FSM inputs
      -- --------------------------------------------------
      --! SOP signals from input lanes 0 and 1
      SOP0              : in std_logic;
      SRC_RDY0          : in std_logic;
      NOT_NULL_SHIFT0   : in std_logic;
      SOP1              : in std_logic;
      SRC_RDY1          : in std_logic;
      NOT_NULL_SHIFT1   : in std_logic;

      --! Destination ready singal
      DST_RDY        : in std_logic;

      --! EOP* signals from Lane 0
      EOP0           : in std_logic;
      EOP_POS_BLK0   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);

      --! EOP* Signals from Lane 1
      EOP1           : in std_logic;
      EOP_POS_BLK1   : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name FSM outputs
      -- --------------------------------------------------
      --! Output Shifting Information for Lane 0 and 1
      --!   00 - inzert zeros (no shift)
      --!   01 - select live data shift
      --!   10 - select shift from the delay register
      SHIFT0         : out std_logic_vector(1 downto 0);
      SHIFT1         : out std_logic_vector(1 downto 0);

      --! Enable signals for write enable into the register
      SHIFT0_REG_EN  : out std_logic;
      SHIFT0_CLR_REG : out std_logic;
      SHIFT1_REG_EN  : out std_logic;
      SHIFT1_CLR_REG : out std_logic;

      --! EOP masking signals
      MASK_EOP0      : out std_logic;
      MASK_EOP1      : out std_logic;

      --! Ouput Line activity
      ACT_LANE0      : out std_logic;
      ACT_LANE1      : out std_logic;

      --! Destination ready signals
      DST_RDY0       : out std_logic;
      DST_RDY1       : out std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLUA_BINDER_GAP_FSM is
   -- Constant declaration ----------------------------------------------------
   --! Max block value
   constant MAX_EOP_BLK_VAL   : std_logic_vector(SOP_POS_WIDTH-1 downto 0) := (others=>'1');
   --! Width of the data block
   constant BLK_WIDTH         : integer := DATA_WIDTH/(2**SOP_POS_WIDTH);
   --! The last eop block, which doesn't evoke shifting of the SOP block to the next
   --! bus word.
   constant MAX_EOP_NO_SHIFT  : std_logic_vector(SOP_POS_WIDTH-1 downto 0) :=
      conv_std_logic_vector((DATA_WIDTH/BLK_WIDTH - 128/BLK_WIDTH - 1) - 1,SOP_POS_WIDTH);
   -- Signal declarations -----------------------------------------------------

   --! State declaration
   type t_state is (WAIT_FOR_DATA,WORD_TRANS,DELAY);

   --! Signals of actual and next state
   signal act_state     : t_state;
   signal next_state    : t_state;

   --! Signal for holding and controling of the input lane
   signal reg_active_lane  : std_logic;
   signal active_lane      : std_logic;
   signal active_lane_en   : std_logic;

   --! Lane ready signals
   signal lane0_data_ready : std_logic;
   signal lane1_data_ready : std_logic;

   --! Short packet detection
   signal lane0_short_packet  : std_logic;
   signal lane1_short_packet  : std_logic;

   --! EOP on lanes has been detected
   signal lane0_eop           : std_logic;
   signal lane1_eop           : std_logic;

   --! Enable signals for destination ready
   signal dst_rdy0_en         : std_logic;
   signal dst_rdy1_en         : std_logic;

   --! Clear and enable signals for shift registers
   signal reg_shift0_wr_en    : std_logic;
   signal reg_shift1_wr_en    : std_logic;
   signal reg_shift0_clr      : std_logic;
   signal reg_shift1_clr      : std_logic;

begin

   --! State register
   state_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            act_state <= WAIT_FOR_DATA;
         else
            act_state <= next_state;
         end if;
      end if;
   end process;

   --! Register for holding of active line
   act_line_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            reg_active_lane <= '0';
         else
            if(active_lane_en = '1' and DST_RDY = '1')then
               reg_active_lane <= active_lane;
            end if;
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------
   -- Output signal generation
   -- -------------------------------------------------------------------------

   --! Generation of lane ready signals
   lane0_data_ready <= SOP0 and SRC_RDY0;
   lane1_data_ready <= SOP1 and SRC_RDY1;

   --! Detection of short packet
   lane0_short_packet <= SOP0 and EOP0 and SRC_RDY0;
   lane1_short_packet <= SOP1 and EOP1 and SRC_RDY1;

   --! Detection of valid EOP
   lane0_eop <= EOP0 and SRC_RDY0;
   lane1_eop <= EOP1 and SRC_RDY1;

   --! Implementation of transition function of the control FSM
   fsm_transp:process(act_state,reg_active_lane,lane0_data_ready,lane1_data_ready,
      DST_RDY,lane0_short_packet,lane1_short_packet,lane0_eop,lane1_eop,
      EOP_POS_BLK0,EOP_POS_BLK1,NOT_NULL_SHIFT0,NOT_NULL_SHIFT1)
   begin
      --! Stay in actual state by default
      next_state <= act_state;

      case act_state is
         when WAIT_FOR_DATA =>
            --if(lane0_data_ready = '1' and DST_RDY = '1' and lane0_short_packet = '0' and
            --   lane1_short_packet = '0')then
            --   -- Long packet is available, go to the word trans state
            --   next_state <= WORD_TRANS;
            --elsif(lane1_data_ready = '1' and DST_RDY = '1' and lane0_short_packet = '0' and
            --      lane1_short_packet = '0')then
            --   -- Long packt is available, go to the word trans state
            --   next_state <= WORD_TRANS;
            --elsif(DST_RDY = '1' and (lane0_short_packet = '1' or lane1_short_packet = '1'))then
            --   -- Short packet is available on the lane.
            --   next_state <= DELAY;
            --end if;
            if((lane0_data_ready = '1' and DST_RDY = '1' and lane0_short_packet = '0' and
               lane1_data_ready = '0') or
               (lane0_data_ready = '1' and DST_RDY = '1' and lane0_short_packet = '0' and
               reg_active_lane = '0'))then
               -- Long packet is available, go to the word trans state
               next_state <= WORD_TRANS;
            elsif((lane1_data_ready = '1' and DST_RDY = '1' and lane1_short_packet = '0' and
                  lane0_data_ready = '0') or
                  (lane1_data_ready = '1' and DST_RDY = '1' and lane1_short_packet = '0' and
                  reg_active_lane = '1'))then
               -- Long packt is available, go to the word trans state
               next_state <= WORD_TRANS;
            elsif(DST_RDY = '1' and (lane0_short_packet = '1' or lane1_short_packet = '1'))then
               -- Short packet is available on the lane.
               next_state <= DELAY;
            end if;

         when WORD_TRANS =>
            if(reg_active_lane = '0')then
               -- Active transfered line is 0
               if((lane0_eop = '1' and DST_RDY = '1' and lane1_data_ready = '0') or
                  (lane0_eop = '1' and DST_RDY = '1' and lane1_data_ready = '1' and
                   EOP_POS_BLK0 > MAX_EOP_NO_SHIFT))then
                  -- No new data available (go to the delay state)
                  next_state <= DELAY;
               end if;
            else
               -- Active transfered line is 1
               if((lane1_eop = '1' and DST_RDY = '1' and lane0_data_ready = '0') or
                  (lane1_eop = '1' and DST_RDY = '1' and lane0_data_ready = '1' and
                   EOP_POS_BLK1 > MAX_EOP_NO_SHIFT))then
                  -- No new data available (go to the initial state)
                  next_state <= DELAY;
               end if;
            end if;

         when DELAY =>
            --This state is only a correction state during which we can receive new data
            --which has to reflect the readed shift between frames.
            if(DST_RDY = '1' and lane0_data_ready = '0' and lane1_data_ready = '0')then
               -- No new data available - go to the wait for data state
               next_state <= WAIT_FOR_DATA;
            elsif((DST_RDY = '1' and lane0_data_ready = '1' and lane0_short_packet = '0'
                     and lane1_data_ready = '0') or
                  (DST_RDY = '1' and lane0_data_ready = '1' and lane0_short_packet = '0'
                     and reg_active_lane = '0') or
                  (DST_RDY = '1' and lane0_data_ready = '1' and lane0_short_packet = '1'
                     and reg_active_lane = '0' and NOT_NULL_SHIFT0 = '1') or
                   (DST_RDY = '1' and lane0_data_ready = '1' and lane0_short_packet = '1'
                     and lane1_data_ready = '0' and NOT_NULL_SHIFT0 = '1'))then
               -- New long packet is available, go to the word transfer state
               next_state <= WORD_TRANS;
            elsif((DST_RDY = '1' and lane1_data_ready = '1' and lane1_short_packet = '0'
                     and lane0_data_ready = '0') or
                  (DST_RDY = '1' and lane1_data_ready = '1' and lane1_short_packet = '0'
                     and reg_active_lane = '1') or
                  (DST_RDY = '1' and lane1_data_ready = '1' and lane1_short_packet = '1'
                     and reg_active_lane = '1' and NOT_NULL_SHIFT1 = '1') or
                   (DST_RDY = '1' and lane1_data_ready = '1' and lane1_short_packet = '1'
                     and lane0_data_ready = '0' and NOT_NULL_SHIFT1 = '1'))then
               -- New long packet is available, go to the word transfer state
               next_state <= WORD_TRANS;
            end if;
            -- else the short packet is detected and we want to stay in the actual state
         when others => null;
      end case;
   end process;

   --! Implementation of output function of the control FSM
   fsm_outp:process(act_state,reg_active_lane,lane0_data_ready,lane1_data_ready,
      lane0_short_packet,lane1_short_packet,lane0_eop,lane1_eop,
      EOP_POS_BLK0,EOP_POS_BLK1,NOT_NULL_SHIFT0,NOT_NULL_SHIFT1)
   begin

      --! Default ioutput values
      SHIFT0      <= (others=>'0');
      SHIFT1      <= (others=>'0');
      reg_shift0_wr_en  <= '0';
      reg_shift1_wr_en  <= '0';
      reg_shift0_clr    <= '0';
      reg_shift1_clr    <= '0';

      ACT_LANE0   <= '0';
      ACT_LANE1   <= '0';

      --! Destinations are ready by default
      dst_rdy0_en    <= '1';
      dst_rdy1_en    <= '1';

      --! Default control values
      active_lane_en <= '0';
      active_lane    <= '0';

      case act_state is
         when WAIT_FOR_DATA =>
            if((lane0_data_ready = '1' and lane1_data_ready = '0') or
               (lane0_data_ready = '1' and reg_active_lane = '0'))then
               -- Lane 0 contains short packet, finish it
               -- The active lane should be lane 0
               ACT_LANE0 <= '1';
               -- Prepare destination ready signal and switch the lane
               if(lane1_data_ready = '1')then
                  dst_rdy1_en <= '0';
               end if;

               -- Set the active lane
               if(lane0_short_packet = '1')then
                  -- Short packet taken from this interface, switch to different and
                  -- remember shifting for next packet
                  active_lane <= '1';
                  reg_shift1_wr_en <= '1';
                  reg_shift0_wr_en <= '1';
               end if;

               active_lane_en <= '1';
            elsif((lane1_data_ready = '1' and lane0_data_ready = '0') or
                  (lane1_data_ready = '1' and reg_active_lane = '1'))then
               -- The active lane should be lane 1
               ACT_LANE1 <= '1';
               -- Prepare destination ready signal and switch the lane
               if(lane0_data_ready = '1')then
                  dst_rdy0_en <= '0';
               end if;

               --Set the active lane
               if(lane1_short_packet = '1')then
                  -- Same as above, look at line if(lane0_short_packet = '1') ..
                  reg_shift0_wr_en <= '1';
                  reg_shift1_wr_en <= '1';
                  active_lane <= '0';
               else
                  active_lane <= '1';
               end if;

               active_lane_en <= '1';
            end if;

            when WORD_TRANS =>
               -- In this state, we perform the transtion of the words, which takes more
               -- than one transaction cycle. We also stay in this state if the shift we
               -- can insert end, gap and start of the new packet on the data line.
               if(reg_active_lane = '0')then
                  -- Active lane is 0
                  ACT_LANE0 <= '1';
                  dst_rdy0_en <= '1';
                  -- Clear shift registers
                  reg_shift0_clr <= '1';
                  reg_shift1_clr <= '1';

                  -- If data are available on lane1, wait on the end of the actual frame
                  if(lane1_data_ready = '1')then
                     dst_rdy1_en <= '0';
                  end if;

                  --! Check if you have available data
                  if(lane0_eop = '1' and EOP_POS_BLK0 <= MAX_EOP_NO_SHIFT and
                     lane1_data_ready = '1')then
                     -- We can match the end of actual frame, gap and start of the new
                     -- frame into the same bus word (use default values of destination
                     -- ready signals)
                     -- Enable the second lane and switch to the new active lane
                     ACT_LANE1      <= '1';
                     active_lane    <= '1';
                     active_lane_en <= '1';
                     dst_rdy1_en    <= '1';
                     -- Enable shifting on lane 1 and take live data
                     SHIFT1 <= "01";
                  elsif(lane0_eop = '1')then
                     -- We have prepared data but the date need to be shifted to the next
                     -- bus word. Don't enable the second line but remeber the shifting
                     -- value, but switch the line. The only enabled line is lane 0
                     reg_shift1_wr_en  <= '1';
                     reg_shift0_wr_en  <= '1';
                     active_lane       <= '1';
                     active_lane_en    <= '1';

                     -- Disable clearing of the shift registers if you need to
                     -- store the the shifting value
                     if(lane1_data_ready = '1' or
                        (lane0_eop = '1' and EOP_POS_BLK0 > MAX_EOP_NO_SHIFT))then
                        -- Clear shift registers
                        reg_shift0_clr <= '0';
                        reg_shift1_clr <= '0';
                     end if;
                  end if;
               else
                  -- Active lane is 1
                  ACT_LANE1 <= '1';
                  dst_rdy1_en <= '1';
                  -- Clear shift register on lane 1
                  reg_shift1_clr <= '1';
                  reg_shift0_clr <= '1';

                  -- If data are available on lane1, wait on the end of the actual frame
                  if(lane0_data_ready = '1')then
                     dst_rdy0_en <= '0';
                  end if;

                  --! Check if you have available data
                  if(lane1_eop = '1' and EOP_POS_BLK1 <= MAX_EOP_NO_SHIFT and lane0_data_ready = '1')then
                     -- We can match the end of actual frame, gap and start of the new
                     -- frame into the same bus word (use default values of destination
                     -- ready signals)
                     -- Enable the second lane and switch to the new active lane
                     ACT_LANE0      <= '1';
                     active_lane_en <= '1';
                     dst_rdy0_en    <= '1';
                     -- Enable shifting on lane 0 and take live data
                     SHIFT0 <= "01";
                  elsif(lane1_eop = '1')then
                     -- We have prepared data but the date need to be shifted to the next
                     -- bus word. Don't enable the second line but remeber the shifting
                     -- value, but switch the line. The only enabled line is lane 1
                     reg_shift0_wr_en  <= '1';
                     reg_shift1_wr_en  <= '1';
                     active_lane_en    <= '1';

                     -- Disable clearing of the shift registers if you need to
                     -- store the the shifting value
                     if(lane0_data_ready = '1' or
                       (lane1_eop = '1' and EOP_POS_BLK1 > MAX_EOP_NO_SHIFT))then
                        -- Clear shift registers
                        reg_shift0_clr <= '0';
                        reg_shift1_clr <= '0';
                     end if;
                  end if;
               end if;

            when DELAY =>
               -- In this state, we have to check the data availability, because we need to
               -- shift incomming data to create gap.
               -- In this state. Enable shifting of all lanes from registers (this helps to
               -- final timing)
               SHIFT0 <= "10";
               SHIFT1 <= "10";

               if(lane0_data_ready = '0' and lane1_data_ready = '0')then
                  -- No data available, clear all shifting registers and
                  -- all destination ready signals should be enabled.
                  reg_shift0_clr <= '1';
                  reg_shift1_clr <= '1';
               elsif((lane0_data_ready = '1' and lane1_data_ready = '0') or
                     (lane0_data_ready = '1' and reg_active_lane = '0'))then
                  -- Lane 0 contains new available data, active the lane 0, enable
                  -- destination ready for lane 0 only. Enable write into the shifting
                  -- register 1 and clear shifting register 0;
                  ACT_LANE0 <= '1';
                  if(lane1_data_ready = '1')then
                     dst_rdy1_en <= '0';
                  end if;

                  -- Set the active lane information
                  if(NOT_NULL_SHIFT0 = '0' and lane0_short_packet = '1')then
                     -- Short packet is using whole bus word, switch to different lane
                     -- to get new data from second port
                     active_lane <= '1';
                  end if;

                  active_lane_en <= '1';

                  -- Deal with information stored in shifting registers
                  reg_shift1_wr_en <= '1';
                  reg_shift0_wr_en <= '1';
               elsif((lane1_data_ready = '1' and lane0_data_ready = '0') or
                     (lane1_data_ready = '1' and reg_active_lane = '1'))then
                  -- Check the lane 1 if you have available any data, active the lane 1,
                  -- enable destination ready for lane 1 only. Enable write into the
                  -- shifting register 0 and clear shifting register 1;
                  ACT_LANE1 <= '1';
                  if(lane0_data_ready = '1')then
                     dst_rdy0_en <= '0';
                  end if;

                  -- Set the active lane information
                  if(NOT_NULL_SHIFT1 = '0' and lane1_short_packet = '1')then
                     active_lane <= '0';
                  else
                     active_lane <= '1';
                  end if;

                  active_lane_en <= '1';

                  -- Deal with information stored in shifting registers
                  reg_shift0_wr_en <= '1';
                  reg_shift1_wr_en <= '1';
               end if;

         when others => null;
      end case;
   end process;

   --! Generation of MASK signals
   MASK_EOP0 <= '0' when((act_state = DELAY or act_state = WORD_TRANS) and
                         lane0_short_packet = '1' and NOT_NULL_SHIFT0 = '1')
                else '1';

   MASK_EOP1 <= '0' when((act_state = DELAY or act_state = WORD_TRANS) and
                         lane1_short_packet = '1' and NOT_NULL_SHIFT1 = '1')
                else '1';

   --! Generation of destination ready signal
   DST_RDY0 <= DST_RDY and dst_rdy0_en;
   DST_RDY1 <= DST_RDY and dst_rdy1_en;

   --! Generatio of control register signals
   SHIFT0_REG_EN     <= DST_RDY and reg_shift0_wr_en;
   SHIFT0_CLR_REG    <= DST_RDY and reg_shift0_clr;
   SHIFT1_REG_EN     <= DST_RDY and reg_shift1_wr_en;
   SHIFT1_CLR_REG    <= DST_RDY and reg_shift1_clr;

end architecture;
