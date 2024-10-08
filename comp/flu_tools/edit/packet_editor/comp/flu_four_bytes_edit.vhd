-- Copyright (C) 2016 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity FOUR_BYTES_EDITOR is
   generic(
      DATA_WIDTH 	   : integer := 512;
      -- offfset block - max 48 bits
      OFFSET_WIDTH   : integer := 10;
      -- support mask
      EN_MASK        : boolean := true
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      PAUSE_EDITING  : in std_logic;
      -- output data
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);

      -- valid input data
      VLD            : in std_logic;
      -- input data
      DATA_IN        : in std_logic_vector(DATA_WIDTH-1 downto 0);

      GET_NEW_PACEKT : out std_logic;
      -- start replace (VLD must be enable)
      START_REPLACE  : in std_logic;
      -- new data
      NEW_DATA       : in std_logic_vector((8*4)-1 downto 0);
      SHIFT          : in std_logic;
      -- offset of four bytes blocks
      IN_OFFSET      : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      -- mask for new data
      MASK           : in std_logic_vector(3 downto 0);
      -- enable editor
      ENABLE_EDIT    : in std_logic;
      -- actual format on flu interface
      FLU_STATE      : in std_logic_vector(2 downto 0);

      EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
   );
end entity;

architecture full of FOUR_BYTES_EDITOR is

   signal zeros               : std_logic_vector(63 downto 0);

   constant num_bytes         : integer := DATA_WIDTH/8;
   constant num_blocks        : integer := num_bytes/4;
   -- signals for ALU_SUB
   signal sub_in1             : std_logic_vector(47 downto 0);
   signal sub_in2             : std_logic_vector(47 downto 0);
   signal sub_out             : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal sub_out_pipe        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal sub_carry           : std_logic;
   signal sub_carry_pipe      : std_logic;
   -- signals for mux_pause
   signal mux_pause_in1       : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_pause_in2       : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_pause_sel       : std_logic_vector(0 downto 0);
   signal mux_pause_out       : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- signals for mux_sub
   signal mux_sub_in1         : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_sub_in2         : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_sub_sel         : std_logic_vector(0 downto 0);
   signal mux_sub_out         : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- signals for mux_out_sub
   signal mux_out_sub_in1     : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_out_sub_in2     : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_out_sub_sel     : std_logic_vector(0 downto 0);
   signal mux_out_sub_out     : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- signal for control mux_out_sub
   signal mux_out_sub_c_out   : std_logic;
   -- signals for mux_inoff_subpipe
   signal mux_inoff_subpipe_in1        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_inoff_subpipe_in2        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_inoff_subpipe_sel        : std_logic_vector(0 downto 0);
   signal mux_inoff_subpipe_out        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal mux_inoff_subpipe_out_pipe   : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   -- out from pipe signals
   signal data_in_pipe        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal new_data_pipe       : std_logic_vector((8*4)-1 downto 0);
   signal mask_pipe           : std_logic_vector(3 downto 0);
   -- convert offset to muxs control signal
   signal in_conv_offset      : std_logic_vector(log2(num_blocks)-1 downto 0);
   signal offset_conv         : std_logic_vector(num_blocks-1 downto 0);
   signal block_sel           : std_logic_vector(num_blocks-1 downto 0);
   signal block_sel_shift     : std_logic_vector(num_blocks-1 downto 0);
   signal block_begin         : std_logic;
   signal block_end           : std_logic;
   signal bytes_sel           : std_logic_vector(num_bytes*2-1 downto 0);
   -- signal for data editor
   signal data_replace_new_data  : std_logic_vector((8*4)-1 downto 0);
   signal data_replace_in        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal data_replace_bytes_sel : std_logic_vector(num_bytes*2-1 downto 0);
   signal data_replace_out       : std_logic_vector(DATA_WIDTH-1 downto 0);
   -- input pipe
   signal in_pipe_data_in        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_pipe_vld            : std_logic;
   signal in_pipe_start_replace  : std_logic;
   signal in_pipe_mask           : std_logic_vector(3 downto 0);
   signal in_pipe_new_data       : std_logic_vector((4*8)-1 downto 0);
   signal in_pipe_in_offset      : std_logic_vector(OFFSET_WIDTH-1 downto 0);

   signal set_pause_not          : std_logic;
   signal mux_pause_in21         : std_logic_vector(mux_pause_in1'LENGTH * 2 - 1 downto 0);
   signal mux_inoff_subpipe_in21 : std_logic_vector(mux_inoff_subpipe_in1'LENGTH * 2 - 1 downto 0);
   signal mux_sub_in21           : std_logic_vector(mux_sub_in1'LENGTH * 2 - 1 downto 0);
   signal mux_out_sub_in21       : std_logic_vector(mux_out_sub_in1'LENGTH * 2 - 1 downto 0);

   signal new_packet             : std_logic;
   signal new_packet_pipe        : std_logic;
   signal flu_state_get_packet   : std_logic;
   signal eop_pos_pipe           : std_logic_vector(EOP_POS'range);
   signal cmp_eop_offset1        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal cmp_eop_offset2        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal cmp_eop_offset         : std_logic;
   signal state_four             : std_logic;
   signal enable_adit_pipe       : std_logic;

   signal in_pipe_state_flu      : std_logic_vector(FLU_STATE'range);
   signal state_flu_pipe         : std_logic_vector(FLU_STATE'range);
   signal in_pipe_shift          : std_logic;
   signal shift_pipe             : std_logic;
begin
   zeros <= (others => '0');

   -- input pipe
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            in_pipe_vld           <= '1';
            in_pipe_start_replace <= '0';
            new_packet_pipe       <= '1';
         elsif(PAUSE_EDITING = '1') then
            in_pipe_data_in       <= DATA_IN;
            in_pipe_vld           <= VLD;
            in_pipe_start_replace <= START_REPLACE;
            in_pipe_mask          <= MASK;
            in_pipe_new_data      <= NEW_DATA;
            in_pipe_in_offset     <= IN_OFFSET;
            in_pipe_state_flu     <= FLU_STATE;
            new_packet_pipe       <= new_packet;
            eop_pos_pipe          <= EOP_POS;
            enable_adit_pipe      <= ENABLE_EDIT;
            in_pipe_shift         <= SHIFT;
         end if;
      end if;
   end process;


   -- compare EOP_POS and input offset
   cmp_eop_offset1 <= zeros(OFFSET_WIDTH-EOP_POS'LENGTH-1+2 downto 0) & eop_pos_pipe(EOP_POS'LENGTH-1 downto 2);
   cmp_eop_offset2 <= sub_out_pipe(OFFSET_WIDTH-1 downto 0) when in_pipe_start_replace = '0' else
                      in_pipe_in_offset;
   cmp_eop_offset  <= '1' when cmp_eop_offset1 < cmp_eop_offset2 else
                      '0';

   -- control signal "next packet"
   process(FLU_STATE, set_pause_not)
   begin
      flu_state_get_packet <= '0';
      if(set_pause_not = '1') then
         if(FLU_STATE = "001" or FLU_STATE = "011") then
            flu_state_get_packet <= '1';
         end if;
      end if;
   end process;

   state_four <= '1' when set_pause_not = '1' and FLU_STATE = "100" and cmp_eop_offset = '1' else
                 '0';

   process(in_pipe_start_replace, sub_carry, flu_state_get_packet, new_packet_pipe)
   begin
      new_packet <= new_packet_pipe;
      if(in_pipe_start_replace = '1') then
         if(sub_carry = '0' or flu_state_get_packet = '1') then
            new_packet <= '1';
         else
            new_packet <= '0';
         end if;
      else
         if(sub_carry = '0' or flu_state_get_packet = '1') then
            new_packet <= '1';
         end if;
      end if;
   end process;
   GET_NEW_PACEKT <= new_packet;

   -- pipe
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         --if (RESET = '1') then

         --else
         if(set_pause_not = '1') then
            data_in_pipe   <= in_pipe_data_in;
            state_flu_pipe <= in_pipe_state_flu;

            sub_carry_pipe <= sub_carry;
            mux_inoff_subpipe_out_pipe <= mux_inoff_subpipe_out;

            if(set_pause_not = '1') then
               sub_out_pipe   <= sub_out;
            end if;

            if(in_pipe_start_replace = '1') then
               new_data_pipe  <= in_pipe_new_data;
               mask_pipe      <= in_pipe_mask;
               shift_pipe     <= in_pipe_shift;
            end if;

         end if;
      end if;
   end process;

   -- sub offset and constant
   --sub_in1 <= zeros(48-OFFSET_WIDTH-1 downto 0) & mux_sub_out;
   --sub_in2 <= conv_std_logic_vector(num_blocks, sub_in2'LENGTH);
   --SUB_ALU: entity work.ALU_DSP
   --generic map(
   --   DATA_WIDTH  => 48,
   --   REG_IN      => 0,
   --   REG_OUT     => 0
   --)
   --port map (
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => sub_in1,
   --   B           => sub_in2,
   --   CE_IN       => '1',
   --   CE_OUT      => '1',
   --   ALUMODE     => "0001",
   --   CARRY_IN    => '0',
   --   CARRY_OUT   => sub_carry,
   --   P           => sub_out
   --);

   sub_out <= mux_sub_out - conv_std_logic_vector(num_blocks, OFFSET_WIDTH);
   sub_carry <= '0' when mux_sub_out < conv_std_logic_vector(num_blocks, OFFSET_WIDTH) else '1';

   -- multiplexing input for SUB_ALU
   mux_sub_in1    <= mux_out_sub_out;
   mux_sub_in2    <= in_pipe_in_offset;
   mux_sub_sel(0) <= '0' when state_four = '1' and enable_adit_pipe = '0' else
                     in_pipe_start_replace;
   --mux_sub_sel(0) <= in_pipe_start_replace;
   MUX_SUB_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => OFFSET_WIDTH,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => mux_sub_in21,--(mux_sub_in2 & mux_sub_in1),
      SEL         => mux_sub_sel,
      DATA_OUT    => mux_sub_out
   );
   mux_sub_in21   <= mux_sub_in2 & mux_sub_in1;

   -- multiplexing output from ALU_SUB
   mux_out_sub_in1    <= mux_pause_out;
   mux_out_sub_in2    <= (others => '1');
   mux_out_sub_sel(0) <= mux_out_sub_c_out when state_four = '0' else
                         '1';
   MUX_OUT_SUB_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => OFFSET_WIDTH,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => mux_out_sub_in21,
      SEL         => mux_out_sub_sel,
      DATA_OUT    => mux_out_sub_out
   );
   mux_out_sub_in21 <= mux_out_sub_in2 & mux_out_sub_in1;

   -- control mux_out_sub
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
               mux_out_sub_c_out <= '1';
         else
            if(flu_state_get_packet = '1') then
               mux_out_sub_c_out <= '1';
            elsif(mux_out_sub_c_out = '1') then
               if(in_pipe_start_replace = '1' and sub_carry = '1') then
                  mux_out_sub_c_out <= '0';
               end if;
            else
               if(sub_carry = '0') then
                  mux_out_sub_c_out <= '1';
               end if;
            end if;
         end if;
      end if;
   end process;

   -- multiplexing between offset input and out from pipe SUB_ALU
   mux_inoff_subpipe_in1    <= sub_out_pipe(OFFSET_WIDTH-1 downto 0);
   mux_inoff_subpipe_in2    <= in_pipe_in_offset;
   mux_inoff_subpipe_sel(0) <= in_pipe_start_replace;
   MUX_INOFF_SUBPIPE_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => OFFSET_WIDTH,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => mux_inoff_subpipe_in21,
      SEL         => mux_inoff_subpipe_sel,
      DATA_OUT    => mux_inoff_subpipe_out
   );
   mux_inoff_subpipe_in21 <= mux_inoff_subpipe_in2 & mux_inoff_subpipe_in1;

   -- pause sub
   set_pause_not     <= in_pipe_vld and PAUSE_EDITING;
   mux_pause_in2     <= sub_out_pipe(OFFSET_WIDTH-1 downto 0);
   mux_pause_in1     <= (others => '1');
   mux_pause_sel(0)  <= set_pause_not;
   MUX_pause_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => OFFSET_WIDTH,
      MUX_WIDTH   => 2
   )
   port map(
      DATA_IN     => mux_pause_in21,
      SEL         => mux_pause_sel,
      DATA_OUT    => mux_pause_out
   );
   mux_pause_in21 <= mux_pause_in2 & mux_pause_in1;

   -- convert offset to control signal for muxs array
   in_conv_offset <= mux_inoff_subpipe_out_pipe(log2(num_blocks)-1 downto 0);

   -- generate sel signals for multiplexers
   data_replace_new_data   <= new_data_pipe;
   data_replace_in         <= data_in_pipe;
   DATA_OUT                <= data_replace_out;
   DATA_EDITOR_inst: entity work.DATA_REPLACE
   generic map (
      DATA_WIDTH  => DATA_WIDTH,
      PIPE_EN     => false,
      DSP_ON      => false
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      EN_PIPE     => '1',
      SHIFT       => shift_pipe,
      NEW_DATA    => data_replace_new_data,
      MASK        => mask_pipe,
      DATA_OUT    => data_replace_out,
      DATA_IN     => data_replace_in,
      DATA_IN_VLD => set_pause_not,
      OFFSET      => in_conv_offset(log2((DATA_WIDTH/8)/4)-1 downto 0),
      OFFSET_VLD  => not sub_carry_pipe,
      FLU_STATE   => in_pipe_state_flu
   );

end architecture;
