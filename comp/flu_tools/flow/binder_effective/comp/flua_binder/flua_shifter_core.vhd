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
entity FLUA_SHIFTER_CORE is
   generic(
      -- FLU Config -----------------------------
      --! FLU protocol generics
      DATA_WIDTH    : integer:= 256;
      SOP_POS_WIDTH : integer:= 2;

      --! Changes for binding with FLU gap,
      --! if short frame with non zero shift is detected,
      --! ignore first EOP because it is not valid, this signal
      --! not masked to reach better frequency.
      FLU_GAP_EN    : boolean := false
   );
   port(
       -- -------------------------------------------------
       -- \name Common interface
       -- -------------------------------------------------
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- --------------------------------------------------
      -- \name Control interface
      -- --------------------------------------------------
      -- Shifting value of SOP_POS; this signal is valid
      -- when RX_SOP is asserted.
      SHIFT_VAL      : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);

      -- --------------------------------------------------
      -- \name Frame Link Unaligned input interface
      -- --------------------------------------------------
      RX_DATA       : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS    : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS    : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP        : in std_logic;
      RX_EOP        : in std_logic;
      RX_SRC_RDY    : in std_logic;
      RX_DST_RDY    : out std_logic;

      -- --------------------------------------------------
      -- \name Frame Link Unaligned output interface
      -- --------------------------------------------------
      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS     : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP         : out std_logic;
      TX_EOP         : out std_logic;
      TX_SRC_RDY     : out std_logic;
      TX_DST_RDY     : in std_logic
   );
end entity;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
architecture FULL of FLUA_SHIFTER_CORE is
   -- Constants declaration ---------------------------------------------------
   constant DATA_BLOCK_WIDTH     : integer := DATA_WIDTH/(2**SOP_POS_WIDTH);
   constant DATA_BLOCK_COUNT     : integer := 2**SOP_POS_WIDTH;

   --! The value of shifted offset
   constant SHIFT_VAL_OFFSET     : integer := (2**SOP_POS_WIDTH)-1;

   -- Signals declaration -----------------------------------------------------
      --! Registers for FLUA flow
   signal reg_flua_data          : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal reg_shift_val          : std_logic_vector(SOP_POS_WIDTH-1 downto 0);

   --! Composition of data shifting bus
   type t_shift_array is array(0 to 2**(SOP_POS_WIDTH+1)-2)
      of std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_shift_bus      : t_shift_array;

   --! Signal for storing of eop moved information. If active, EOP was moved
   --! to the next word.
   signal eop_moved_en           : std_logic;
   signal reg_eop_moved_en       : std_logic;
   signal eop_pos_blk            : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal ext_eop_pos_blk        : std_logic_vector(SOP_POS_WIDTH downto 0);
   signal ext_reg_shift_val      : std_logic_vector(SOP_POS_WIDTH downto 0);
   signal sum_new_eop_pos        : std_logic_vector(SOP_POS_WIDTH downto 0);
   signal reg_short_packet_det   : std_logic;

   --! Signals for computation of new eop_pos value
   signal new_eop_pos_blk        : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal new_eop_pos_blk_live   : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal new_eop_pos            : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal new_eop_pos_live       : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal reg_new_eop_pos        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal reg_new_eop_pos_live   : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

   --! Data shift value
   signal reg_data_shift_val     : std_logic_vector(SOP_POS_WIDTH downto 0);
   signal act_data_shift_val     : std_logic_vector(SOP_POS_WIDTH downto 0);
   signal ext_data_shift_val     : std_logic_vector(SOP_POS_WIDTH downto 0);

begin

   NO_GAP_RX_DST_RDY_GEN:if(FLU_GAP_EN = false)generate
      --! Copy destination ready signal from the TX side
      RX_DST_RDY <=  '0' when(reg_eop_moved_en = '1')
                     else TX_DST_RDY;
   end generate;

   GAP_RX_DST_RDY_GEN:if(FLU_GAP_EN = true)generate
      --! Copy destination ready signal from the TX side, stop the transfer
      --! if:
      --! * EOP is moved to the next bus word
      --! * Start of the new frame is detected
      RX_DST_RDY <=  '0' when((reg_eop_moved_en = '1' or reg_short_packet_det = '1') and
                              RX_SRC_RDY = '1' and RX_SOP = '1')
                     else TX_DST_RDY;

      --! \brief Detection of situation with short packet
      short_packet_det_regp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               reg_short_packet_det <= '0';
            else
               if(TX_DST_RDY = '1' and reg_short_packet_det = '1')then
                  -- Everything with short packet was dealed in this clock cycle
                  reg_short_packet_det <= '0';
               elsif(RX_SRC_RDY = '1' and TX_DST_RDY = '1' and RX_SOP = '1' and RX_EOP = '1'
                  and SHIFT_VAL > 0 and reg_short_packet_det = '0')then
                  -- Short packet with shifting was detected, notice that the shortest
                  -- packet equals to 60 bytes (512 bit data bus equals to 64 bytes)
                  reg_short_packet_det <= '1';
               end if;
            end if;
         end if;
      end process;
   end generate;

   --! Input FLUA register. Only valid data is stored.
   flua_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RX_SRC_RDY = '1' and TX_DST_RDY = '1')then
            -- Rewrite data if and only if destination and source are ready
            reg_flua_data <= RX_DATA;
         end if;
      end if;
   end process;

   --! Input shift value register
   flua_shift_repg:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            reg_shift_val <= (others=>'0');
         else
            if(RX_SRC_RDY = '1' and TX_DST_RDY = '1' and RX_SOP = '1')then
               reg_shift_val <= SHIFT_VAL;
            end if;
         end if;
      end if;
   end process;

   -- Generation of output SOP* signals ---------------------------------------
   -- TODO: Redesign SOP* signaling
   --! Generation of output SOP_POS
   NO_GAP_SOP_GEN:if(FLU_GAP_EN = false)generate
      TX_SOP_POS  <= SHIFT_VAL;
      TX_SOP      <= RX_SOP and not(reg_eop_moved_en);
   end generate;

   GAP_SOP_GEN:if(FLU_GAP_EN = true)generate
      TX_SOP_POS  <= SHIFT_VAL;
      TX_SOP      <= RX_SOP and not(reg_eop_moved_en or reg_short_packet_det);
   end generate;

   -- Deal with data shifting -------------------------------------------------
   --! Generation of all possible shiftings
   SHIFT_IN_ACT_WORD_GEN:for i in 0 to 2**SOP_POS_WIDTH-1 generate
      -- No shift at all (copy actual input)
      NO_SHIFT_GEN:if(i = 0)generate
         data_shift_bus(i) <= RX_DATA;
      end generate;

      SHIFT_GEN:if(i /= 0)generate
         data_shift_bus(i)(DATA_BLOCK_COUNT*DATA_BLOCK_WIDTH-1 downto i*DATA_BLOCK_WIDTH)
            <= RX_DATA((DATA_BLOCK_COUNT-i)*DATA_BLOCK_WIDTH-1 downto 0);

         -- Rest will be filled with zeros
         data_shift_bus(i)(i*DATA_BLOCK_WIDTH-1 downto 0) <= (others=>'0');
      end generate;
   end generate;

   --Generation of all shiftings in
   SHIFT_IN_REG_WORD_GEN:for i in 0 to 2**SOP_POS_WIDTH-2 generate
      data_shift_bus(2**SOP_POS_WIDTH+i) <=
      RX_DATA(DATA_BLOCK_WIDTH*(DATA_BLOCK_COUNT-1-i)-1 downto 0)
      &
      reg_flua_data(DATA_BLOCK_WIDTH*DATA_BLOCK_COUNT-1
                    downto
                    DATA_BLOCK_WIDTH*(DATA_BLOCK_COUNT-1-i));
   end generate;

   --! Generation of data shifting value
   data_shift_val_reg:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RESET = '1')then
            reg_data_shift_val <= (others=>'0');
         else
            if(RX_SRC_RDY = '1' and TX_DST_RDY = '1' and RX_SOP = '1' and SHIFT_VAL /= 0)then
               -- Compute new data shifting value
               reg_data_shift_val <= ext_data_shift_val + SHIFT_VAL_OFFSET;
            elsif(RX_SRC_RDY = '1' and TX_DST_RDY = '1' and RX_SOP = '1' and SHIFT_VAL = 0)then
               reg_data_shift_val  <= (others=>'0');
            end if;
         end if;
      end if;
   end process;

   --! Compose extended SHIFT_VAL
   ext_data_shift_val <= '0' & SHIFT_VAL;

   --! Selection of right Data shift
   GAP_ACT_DATA_SHIFT_VAL:if(FLU_GAP_EN = true)generate
      act_data_shift_val <=
         ext_data_shift_val when(RX_SRC_RDY = '1' and RX_SOP = '1' and
                                 reg_eop_moved_en = '0' and reg_short_packet_det = '0')
         else reg_data_shift_val;
   end generate;

   NO_GAP_ACT_DATA_SHIFT_VAL:if(FLU_GAP_EN = false)generate
      act_data_shift_val <=
         ext_data_shift_val when(RX_SRC_RDY = '1' and RX_SOP = '1' and
                                 reg_eop_moved_en = '0')
         else reg_data_shift_val;
   end generate;

   --! Selection of right shift block
   TX_DATA <= data_shift_bus(conv_integer(UNSIGNED(act_data_shift_val)));

   -- Deal with signalization of EOP* signalization ---------------------------
   --! Generation of eop_moved signal(look at carry singal on position SOP_POS_WIDTH+1)
   ext_eop_pos_blk      <= '0' & eop_pos_blk;
   ext_reg_shift_val    <= '0' & reg_shift_val;
   sum_new_eop_pos      <= ext_eop_pos_blk + ext_reg_shift_val;
   eop_moved_en   <=  sum_new_eop_pos(SOP_POS_WIDTH);
   eop_pos_blk    <= RX_EOP_POS(log2(DATA_WIDTH/8)-1 downto log2(DATA_WIDTH/8)-SOP_POS_WIDTH);

   NO_EOP_MOVED_REG:if(FLU_GAP_EN = false)generate
      --! Register for storing of EOP_MOVED information
      eop_moved_en_regp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               reg_eop_moved_en <= '0';
            else
               if(TX_DST_RDY = '1' and reg_eop_moved_en = '1')then
                  reg_eop_moved_en <= '0';
               elsif(RX_EOP = '1'  and RX_SRC_RDY = '1' and TX_DST_RDY = '1')then
                  -- EOP moved was detected, we need to store infortmation about
                  -- shifting of eop to the new word
                  reg_eop_moved_en <= eop_moved_en;
               end if;
            end if;
         end if;
      end process;
   end generate;

   EOP_MOVED_REG:if(FLU_GAP_EN = true)generate
      --! Register for storing of EOP_MOVED information
      eop_moved_en_regp:process(CLK)
      begin
         if(CLK = '1' and CLK'event)then
            if(RESET = '1')then
               reg_eop_moved_en <= '0';
            else
               --if((RX_SRC_RDY = '1' and TX_DST_RDY = '1' and reg_eop_moved_en = '1') or
               if((TX_DST_RDY = '1' and reg_eop_moved_en = '1') or
                  (reg_short_packet_det = '1'))then
                  reg_eop_moved_en <= '0';
               elsif(RX_EOP = '1'  and RX_SRC_RDY = '1' and TX_DST_RDY = '1')then
                  -- EOP moved was detected, we need to store infortmation about
                  -- shifting of eop to the new word
                  reg_eop_moved_en <= eop_moved_en;
               end if;
            end if;
         end if;
      end process;
   end generate;

   --! New computed EOP_POS value
   new_eop_pos_blk <=  eop_pos_blk + reg_shift_val;
      -- Live version of previous signal (information is available one clock earlier)
   new_eop_pos_blk_live <= eop_pos_blk + SHIFT_VAL;

   --! Composition of new EOP_POS value
   new_eop_pos <= new_eop_pos_blk &
                  RX_EOP_POS(log2(DATA_WIDTH/8)-SOP_POS_WIDTH-1 downto 0);
      -- Live version of previous signal (information is available one clock earlier)
   new_eop_pos_live <= new_eop_pos_blk_live &
                       RX_EOP_POS(log2(DATA_WIDTH/8)-SOP_POS_WIDTH-1 downto 0);

   --! Register for storing of new EOP_POS value
   new_eop_pos_regp:process(CLK)
   begin
      if(CLK = '1' and CLK'event)then
         if(RX_SRC_RDY = '1' and TX_DST_RDY = '1')then
            reg_new_eop_pos <= new_eop_pos;
            reg_new_eop_pos_live <= new_eop_pos_live;
         end if;
      end if;
   end process;

   NO_GAP_OUTPUT_GEN:if(FLU_GAP_EN  = false)generate
      --! Switch right EOP_POS value to output
      TX_EOP_POS <= RX_EOP_POS when (RX_SOP = '1' and RX_EOP = '1' and RX_SRC_RDY = '1' and reg_eop_moved_en = '0')else
                    reg_new_eop_pos when(reg_eop_moved_en = '1') else
                    new_eop_pos;

      --! Switch right EOP value to output
      TX_EOP <= RX_EOP when (
                  (RX_SRC_RDY = '1' and RX_SOP = '1' and RX_EOP = '1') or
                  (RX_SRC_RDY = '1' and RX_SOP = '0' and RX_EOP = '1' and eop_moved_en = '0')
                ) else reg_eop_moved_en;

      -- Deal with signalization of RX_SRC_RDY signal
      TX_SRC_RDY <= '1'  when(reg_eop_moved_en = '1')
                    else RX_SRC_RDY;
   end generate;

   GAP_OUTPUT_GEN:if(FLU_GAP_EN = true)generate
      --! Switch right EOP_POS value to output
      TX_EOP_POS <= RX_EOP_POS when (RX_SOP = '1' and RX_EOP = '1' and RX_SRC_RDY = '1' and
                                     reg_eop_moved_en = '0' and reg_short_packet_det = '0')else
                    reg_new_eop_pos when(reg_eop_moved_en = '1' and reg_short_packet_det = '0') else
                    reg_new_eop_pos_live when(reg_short_packet_det = '1')else
                    new_eop_pos;

      --! Switch right EOP value to output
      TX_EOP <= RX_EOP when (
                  (RX_SRC_RDY = '1' and RX_SOP = '1' and RX_EOP = '1') or
                  (RX_SRC_RDY = '1' and RX_SOP = '0' and RX_EOP = '1' and eop_moved_en = '0'))
               else '1' when(reg_short_packet_det = '1')
               else reg_eop_moved_en;

      -- Deal with signalization of RX_SRC_RDY signal
      TX_SRC_RDY <= '1'  when(reg_eop_moved_en = '1' or reg_short_packet_det = '1')
                    else RX_SRC_RDY;
   end generate;

end architecture;
