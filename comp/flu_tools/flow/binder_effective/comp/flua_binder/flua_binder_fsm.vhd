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
entity FLUA_BINDER_FSM is
   generic(
      --! FLUA Generics (needed in control FSM)
      SOP_POS_WIDTH  : integer := 2
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
      SOP0           : in std_logic;
      SRC_RDY0       : in std_logic;
      SOP1           : in std_logic;
      SRC_RDY1       : in std_logic;

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
      SHIFT0         : out std_logic;
      SHIFT1         : out std_logic;

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
architecture FULL of FLUA_BINDER_FSM is
   -- Constant declaration ----------------------------------------------------
   --! Max block value
   constant MAX_EOP_BLK_VAL   : std_logic_vector(SOP_POS_WIDTH-1 downto 0) := (others=>'1');

   -- Signal declarations -----------------------------------------------------

   --! State declaration
   type t_state is (WAIT_FOR_DATA,WORD_TRANS);

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
      DST_RDY,lane0_short_packet,lane1_short_packet,lane0_eop,lane1_eop)
   begin
      --! Stay in actual state by default
      next_state <= act_state;

      case act_state is
         when WAIT_FOR_DATA =>
            if(lane0_data_ready = '1' and DST_RDY = '1' and lane0_short_packet = '0')then
               -- Lane 0 is ready and we are not transfering short packet
               next_state <= WORD_TRANS;
            elsif(lane1_data_ready = '1' and DST_RDY = '1' and lane1_short_packet = '0')then
               -- Lane 1 is ready and we are not transfering short packet
               next_state <= WORD_TRANS;
            end if;

         when WORD_TRANS =>
            if(reg_active_lane = '0')then
               -- Active transfered line is 0
               if(lane0_eop = '1' and lane1_data_ready = '0' and DST_RDY = '1')then
                  -- No new data available (go to the initial state)
                  next_state <= WAIT_FOR_DATA;
               end if;

            else
               -- Active transfered line is 1
               if(lane1_eop = '1' and lane0_data_ready = '0' and DST_RDY = '1')then
                  -- No new data available (go to the initial state)
                  next_state <= WAIT_FOR_DATA;
               end if;
            end if;

         when others => null;
      end case;
   end process;

   --! Implementation of output function of the control FSM
   fsm_outp:process(act_state,reg_active_lane,lane0_data_ready,lane1_data_ready,
      DST_RDY,lane0_short_packet,lane1_short_packet,lane0_eop,lane1_eop,
      EOP_POS_BLK0,EOP_POS_BLK1)
   begin

      --! Default output values
      SHIFT0      <= '0';
      SHIFT1      <= '0';
      ACT_LANE0   <= '0';
      ACT_LANE1   <= '0';

      --! Destinations are ready by default
      DST_RDY0    <= '1';
      DST_RDY1    <= '1';

      --! Default control values
      active_lane_en <= '0';
      active_lane    <= '0';

      case act_state is
         when WAIT_FOR_DATA =>
            -- In this state, all input chanels are ready (DST_RDY* = '1');
            -- We are waiting on first input channel (the second channel will be)
            -- In this state, we can process only one short packet or we can transfer
            -- one packet (longer than one word).
               -- Handle short packets
            if(lane0_short_packet = '1' and lane1_short_packet = '1')then
               --Both lanes contains short packets (take the packet from the next input)
               if(reg_active_lane = '0')then
                  --Select input from lane 1 (wait on lane 0)
                  DST_RDY0 <= '0';
                  DST_RDY1 <= DST_RDY;
                  -- Set new active lane (case with short packets differs from the case
                  -- with longer packets)
                  active_lane    <= '1';
                  active_lane_en <= '1';
                  ACT_LANE1 <= '1';
               else
                  -- Select input from lane 0 (waint on lane 1)
                  DST_RDY0 <= DST_RDY;
                  DST_RDY1 <= '0';
                  -- Set new active lane
                  active_lane_en <= '1';
                  ACT_LANE0 <= '1';
               end if;
            elsif(lane0_short_packet = '1')then
               --Send the short packet on lane 0
               DST_RDY0 <= DST_RDY;
               ACT_LANE0 <= '1';

               if(lane1_data_ready = '1')then
                  --Switch the lane, because we have new
                  --available data
                  active_lane_en <= '1';
                  active_lane <= '1';
                  DST_RDY1 <= '0';
               else
                  -- Restart the active line value
                  active_lane_en <= '1';
                  active_lane <= '0';
               end if;
            elsif(lane1_short_packet = '1')then
               -- Send the short packet on lane 1, if data available on
               -- second line, switch
               DST_RDY1 <= DST_RDY;
               ACT_LANE1 <= '1';

               if(lane0_data_ready = '1')then
                  --Switch the lane, because we have new
                  --available data
                  active_lane_en <= '1';
                  active_lane <= '0';
                  DST_RDY0 <= '0';
               else
                  -- Restart he active line
                  active_lane_en <= '1';
                  active_lane <= '0';
               end if;
            -- Handle packets of normal length ---------------------------
            elsif(lane0_data_ready = '1' and lane1_data_ready = '1')then
               -- Both lanes are ready, select output from lane 0 by default
               DST_RDY0       <= DST_RDY;
               -- Setup update information
               active_lane_en <= '1';
               -- Disable lane 1
               DST_RDY1       <= '0';
               -- Enable Lane 0 on output
               ACT_LANE0 <= '1';
            elsif(lane0_data_ready = '1')then
               -- Lane 0 is ready, select the output
               DST_RDY0 <= DST_RDY;
               -- Setup lane information
               active_lane_en <= '1';
               -- Enable Lane 0 on output
               ACT_LANE0 <= '1';
            elsif(lane1_data_ready = '1')then
               -- Lane 1 is ready, select the output
               DST_RDY1 <= DST_RDY;
               -- Setup lane information
               active_lane <= '1';
               active_lane_en <= '1';
               -- Enable lane 1 on output
               ACT_LANE1 <= '1';
            end if;

         when WORD_TRANS =>
            -- In this state, we can mix two chanels together or continue in sending of the
            -- frame.
            if(reg_active_lane = '0')then
               -- Copy destination ready signal
               DST_RDY0 <= DST_RDY;
               -- Activate output lane 0
               ACT_LANE0 <= '1';

               if(lane0_short_packet = '1')then
                  -- We want to transfer a short packet on lane 0
                  if(lane1_data_ready = '1')then
                     -- Lane 1 has a data, stop the transfer and wait
                     DST_RDY1 <= '0';
                     --Switch the line
                     active_lane <= '1';
                     active_lane_en <= '1';
                  end if;
               else
                  -- We want to transfer longer packet on lane 0
                  if(lane1_data_ready = '1' and lane0_eop = '0')then
                     -- Data transfer is running, lane 1 contains new data;
                     -- stop them and wait
                     DST_RDY1 <= '0';
                  elsif(lane1_data_ready = '1' and lane1_short_packet = '0' and
                        EOP_POS_BLK0 /= MAX_EOP_BLK_VAL and lane0_eop = '1')then
                     -- We have ready new packet, which is not the short one
                     -- and which can be put on the line
                     DST_RDY1 <= DST_RDY;
                     ACT_LANE1 <= '1';
                     active_lane <= '1';
                     active_lane_en <= '1';
                     -- Set new shifting value
                     --SHIFT1 <= shift_lookup_mem(conv_integer(EOP_POS_BLK0));
                     SHIFT1 <= '1';
                  elsif((lane1_short_packet = '1' and lane0_eop = '1') or
                        (lane1_data_ready = '1' and lane0_eop = '1' and EOP_POS_BLK0 = MAX_EOP_BLK_VAL))then
                     -- We want to insert short packet or we can't insert the
                     -- packet becasu we don't have possibility to insert the
                     -- frame, as a result hold the lane 1 swith the active lane
                     DST_RDY1 <= '0';
                     active_lane <= '1';
                     active_lane_en <= '1';
                  elsif(lane0_data_ready = '0' and lane1_data_ready = '0' and lane0_eop = '1')then
                     -- No new data, restart the active lane to 0
                     active_lane <= '0';
                     active_lane_en <= '1';
                  end if;
               end if;

            else
               -- Copy destination ready signal
               DST_RDY1 <= DST_RDY;
               -- Activate output lane 0
               ACT_LANE1 <= '1';

               if(lane1_short_packet = '1')then
                  -- We want to transfer a short packet on lane 0
                  if(lane0_data_ready = '1')then
                     -- Lane 0 has a data, stop the transfer and wait
                     DST_RDY0 <= '0';
                     --Switch the line
                     active_lane <= '0';
                     active_lane_en <= '1';
                  end if;
               else
                  -- We want to transfer longer packet on lane 1
                  if(lane0_data_ready = '1' and lane1_eop = '0')then
                     -- Data transfer is running, lane 1 contains new data;
                     -- stop them and wait
                     DST_RDY0 <= '0';
                  elsif(lane0_data_ready = '1' and lane0_short_packet = '0' and
                        EOP_POS_BLK1 /= MAX_EOP_BLK_VAL and lane1_eop = '1')then
                     -- We have ready new packet, which is not the short one
                     -- and which can be put on the line
                     DST_RDY0 <= DST_RDY;
                     ACT_LANE0 <= '1';
                     active_lane <= '0';
                     active_lane_en <= '1';
                     -- Set new shifting value
                     --SHIFT0 <= shift_lookup_mem(conv_integer(EOP_POS_BLK1));
                     SHIFT0 <= '1';
                  elsif((lane0_short_packet = '1' and lane1_eop = '1') or
                        (lane0_data_ready = '1' and lane1_eop = '1' and EOP_POS_BLK1 = MAX_EOP_BLK_VAL))then
                     -- We want to insert short packet or we can't insert the
                     -- packet becasu we don't have possibility to insert the
                     -- frame, as a result hold the lane 1 swith the active lane
                     DST_RDY0 <= '0';
                     active_lane <= '0';
                     active_lane_en <= '1';
                  elsif(lane0_data_ready = '0' and lane1_data_ready = '0' and lane1_eop = '1')then
                     -- No new data, restart the active lane to 0
                     active_lane <= '0';
                     active_lane_en <= '1';
                  end if;
               end if;
            end if;

         when others => null;
      end case;
   end process;

end architecture;
