-- packet_editor_arch.vhd: architecture of packet editor
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

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of PACKET_EDITOR_L is
   constant sop_pos_num       : integer := 2**SOP_POS_WIDTH;
	constant out_pipe_width    : integer := 1+1+SOP_POS_WIDTH+log2(DATA_WIDTH/8);
   constant num_bytes         : integer := DATA_WIDTH/8;
   constant num_blocks        : integer := num_bytes/4;

   signal zeros               : std_logic_vector(511 downto 0);

   signal editor_pause        : std_logic;
   signal editor_data_out     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal editor_in_vld       : std_logic;
   signal editor_data_in      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal editor_in_offset    : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal editor_mask         : std_logic_vector(3 downto 0);
   signal editor_new_data     : std_logic_vector((4*8)-1 downto 0);
   signal editor_next_packet  : std_logic;
   signal split_flu           : std_logic;
   signal split_flu_reg       : std_logic;
   signal in_enable           : std_logic;
   signal in_enable_zero      : std_logic;
   signal editor_start        : std_logic;
   signal enable_editor       : std_logic;
   signal new_data_editor     : std_logic_vector((8*4)-1 downto 0);
   signal mask_editor         : std_logic_vector(3 downto 0);
   signal offset_in_editor    : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal offset_editor       : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal rx_sop_pos_editor   : std_logic_vector(RX_SOP_POS'range);
   signal rx_eop_pos_editor   : std_logic_vector(RX_EOP_POS'range);
   signal data_in_editor      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sop_editor          : std_logic;
   signal eop_editor          : std_logic;
   signal src_rdy_editor      : std_logic;
   signal rx_eop_pos_pipe     : std_logic_vector(RX_EOP_POS'range);
   signal rx_sop_pos_pipe     : std_logic_vector(RX_SOP_POS'range);
   signal src_rdy_pipe        : std_logic;
   signal rx_eop_pos_pipe2    : std_logic_vector(RX_EOP_POS'range);
   signal rx_sop_pos_pipe2    : std_logic_vector(RX_SOP_POS'range);
   signal src_rdy_pipe2       : std_logic;
   signal eop_pipe            : std_logic;
   signal eop_pipe2           : std_logic;
   signal sop_pipe            : std_logic;
   signal sop_pipe2           : std_logic;
   signal tx_dst_rdy_editor   : std_logic;
   signal zero_offset         : std_logic;
   signal editor_low_offset   : std_logic;

   signal mux_sop_in          : std_logic_vector(5*sop_pos_num-1 downto 0);
   signal mux_sop_sel         : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal mux_sop_out         : std_logic_vector(5-1 downto 0);
   signal add_in1             : std_logic_vector(47 downto 0);
   signal add_in2             : std_logic_vector(47 downto 0);
   signal add_out             : std_logic_vector(47 downto 0);

   signal offset_sub_in1      : std_logic_vector(47 downto 0);
   signal offset_sub_in2      : std_logic_vector(47 downto 0);
   signal offset_sub_out      : std_logic_vector(47 downto 0);
   signal offset_alu_pipe_out : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal big_offset          : std_logic;
   signal big_offset_pipe     : std_logic;
   signal in_enable_next      : std_logic;
   signal split_flu_first     : std_logic;
   signal mask_editor_pipe    : std_logic_vector(3 downto 0);
   signal new_data_editor_pipe   : std_logic_vector((8*4)-1 downto 0);

   signal shift_editor : std_logic;
   signal shift_editor_pipe : std_logic;
   signal editor_shift : std_logic;

   signal flu_state           : std_logic_vector(2 downto 0);
   signal cmp_eop_sop_insop   : std_logic_vector(RX_EOP_POS'range);
   signal cmp_eop_sop         : std_logic;
begin
   zeros <= (others => '0');

   cmp_eop_sop_insop <= rx_sop_pos_pipe & zeros(RX_EOP_POS'length-SOP_POS_WIDTH-1 downto 0);
   cmp_eop_sop <= '1' when rx_eop_pos_pipe > cmp_eop_sop_insop else '0';

   -- get actual format from flu interface
   flu_state <= "000" when eop_pipe = '0' and sop_pipe = '0' else
                "001" when eop_pipe = '1' and sop_pipe = '0' else
                "010" when eop_pipe = '0' and sop_pipe = '1' else
                "011" when eop_pipe = '1' and sop_pipe = '1' and cmp_eop_sop = '1' else
                "100";

   -- input pipe
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            enable_editor        <= '0';
            src_rdy_pipe         <= '0';
            src_rdy_pipe2        <= '0';
            src_rdy_editor       <= '0';
            big_offset_pipe      <= '0';
         else
            if(tx_dst_rdy_editor = '1') then
               enable_editor     <= EN_REPLACE;
               new_data_editor   <= NEW_DATA;
               shift_editor      <= SHIFT;
               mask_editor       <= MASK;
               offset_in_editor  <= OFFSET;
               rx_sop_pos_editor <= RX_SOP_POS;
               rx_eop_pos_editor <= RX_EOP_POS;
               data_in_editor    <= RX_DATA;
               sop_editor        <= RX_SOP;
               eop_editor        <= RX_EOP;
               src_rdy_editor    <= RX_SRC_RDY;
            end if;

            if(TX_DST_RDY = '1') then
               rx_eop_pos_pipe      <= rx_eop_pos_editor;
               rx_sop_pos_pipe      <= rx_sop_pos_editor;
               src_rdy_pipe         <= src_rdy_editor;
               rx_eop_pos_pipe2     <= rx_eop_pos_pipe;
               rx_sop_pos_pipe2     <= rx_sop_pos_pipe;
               src_rdy_pipe2        <= src_rdy_pipe;
               eop_pipe2            <= eop_pipe;
               sop_pipe2            <= sop_pipe;
               big_offset_pipe      <= big_offset;
               mask_editor_pipe     <= mask_editor;
               new_data_editor_pipe <= new_data_editor;
               shift_editor_pipe    <= shift_editor;
            end if;
         end if;
      end if;
   end process;

   RX_DST_RDY  <= tx_dst_rdy_editor;

   TX_DATA     <= editor_data_out;
   TX_SOP_POS  <= rx_sop_pos_pipe2;
   TX_EOP_POS  <= rx_eop_pos_pipe2;
   TX_EOP      <= eop_pipe2;
   TX_SOP      <= sop_pipe2;
   TX_SRC_RDY  <= src_rdy_pipe2;

   -- convert constants to std_logic_vector
   GEN_SOP_MUX_IN: for I in 0 to sop_pos_num-1 generate
      mux_sop_in(4+I*5 downto I*5) <= conv_std_logic_vector(16/sop_pos_num*I, 5);
   end generate;

   mux_sop_sel    <= rx_sop_pos_editor;
   -- select constant sop pos
   MUX_SOP_OFFSET: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => 5,
      MUX_WIDTH   => 2**SOP_POS_WIDTH
   )
   port map(
      DATA_IN     => mux_sop_in,
      SEL         => mux_sop_sel,
      DATA_OUT    => mux_sop_out
   );

   -- add offset and constant
   add_in1 <= zeros(48-5-1 downto 0) & mux_sop_out;
   add_in2 <= zeros(48-OFFSET_WIDTH-1 downto 0) & offset_in_editor;
   --OFFSET_ADD: entity work.ALU_DSP
   --generic map(
   --   DATA_WIDTH  => 48,
   --   REG_IN      => 0,
   --   REG_OUT     => 0
   --)
   --port map (
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => add_in1,
   --   B           => add_in2,
   --   CE_IN       => '1',
   --   CE_OUT      => '1',
   --   ALUMODE     => "0000",
   --   CARRY_IN    => '0',
   --   CARRY_OUT   => open,
   --   P           => add_out
   --);

   add_out <= add_in1 + add_in2;
   offset_editor <= add_out(OFFSET_WIDTH-1 downto 0);

   process(offset_editor(OFFSET_WIDTH-1 downto 4), TX_DST_RDY)
   begin
      zero_offset <= '0';
      if(TX_DST_RDY = '1') then
         if(offset_editor(OFFSET_WIDTH-1 downto 4) = conv_std_logic_vector(0,OFFSET_WIDTH-4)) then
            zero_offset <= '1';
         end if;
      end if;
   end process;

   in_enable <= src_rdy_editor and sop_editor and enable_editor;
   process(in_enable, editor_next_packet, TX_DST_RDY)
   begin
      split_flu_first <= '0';
      if(TX_DST_RDY = '1') then
         if(in_enable = '1' and editor_next_packet = '0') then
            split_flu_first <= '1';
         end if;
      end if;
   end process;

   in_enable_next <= RX_SRC_RDY and (not RX_SOP or not EN_REPLACE);

   process(in_enable_next, zero_offset, split_flu_first)
   begin
      if(zero_offset = '0' and in_enable_next = '1' and split_flu_first = '1') then
         split_flu   <= '0';
         big_offset  <= '1';
      else
         split_flu   <= split_flu_first;
         big_offset  <= '0';
      end if;
   end process;

   tx_dst_rdy_editor <= TX_DST_RDY and (not split_flu);

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(TX_DST_RDY = '1') then
            if(split_flu = '1') then
               sop_pipe <= '0';
            else
               sop_pipe <= sop_editor;
            end if;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(TX_DST_RDY = '1') then
            if(split_flu_reg = '1') then
               eop_pipe <= '0';
            else
               eop_pipe <= eop_editor;
            end if;
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            split_flu_reg <= '0';
         elsif(TX_DST_RDY = '1') then
            split_flu_reg <= split_flu;
         end if;
      end if;
   end process;

   process(split_flu, in_enable, big_offset_pipe, big_offset)
   begin
      if(split_flu = '1') then
         editor_start <= '0';
      else
         editor_start <= (in_enable and not big_offset) or big_offset_pipe;
      end if;
   end process;


   offset_sub_in1 <= zeros(48-OFFSET_WIDTH-1 downto 0) & offset_editor;
   offset_sub_in2 <= conv_std_logic_vector(num_blocks, 48);
   OFFSET_ALU: entity work.ALU_DSP
   generic map(
      DATA_WIDTH  => 48,
      REG_IN      => 0,
      REG_OUT     => 1
   )
   port map (
      CLK         => CLK,
      RESET       => RESET,
      A           => offset_sub_in1,
      B           => offset_sub_in2,
      CE_IN       => '1',
      CE_OUT      => TX_DST_RDY,
      ALUMODE     => "0001",
      CARRY_IN    => '0',
      CARRY_OUT   => open,
      P           => offset_sub_out
   );

   offset_alu_pipe_out <= offset_sub_out(OFFSET_WIDTH-1 downto 0);
   process(offset_editor, offset_alu_pipe_out, big_offset_pipe)
   begin
      if(big_offset_pipe = '1') then
         editor_in_offset <= offset_alu_pipe_out;
      else
         editor_in_offset <= offset_editor;
      end if;
   end process;

   process(new_data_editor_pipe, new_data_editor, big_offset_pipe)
   begin
      if(big_offset_pipe = '1') then
         editor_new_data <= new_data_editor_pipe;
      else
         editor_new_data <= new_data_editor;
      end if;
   end process;

   process(ALL)
   begin
      if(big_offset_pipe = '1') then
         editor_shift <= shift_editor_pipe;
      else
         editor_shift <= shift_editor;
      end if;
   end process;

   process(mask_editor, mask_editor_pipe, big_offset_pipe)
   begin
      if(big_offset_pipe = '1') then
         editor_mask <= mask_editor_pipe;
      else
         editor_mask <= mask_editor;
      end if;
   end process;

   -- connect four bytes editor
   editor_pause         <= TX_DST_RDY;
   editor_in_vld        <= src_rdy_editor;
   editor_data_in       <= data_in_editor;
   FOUR_BYTES_EDITOR : entity work.FOUR_BYTES_EDITOR
   generic map (
      DATA_WIDTH        => DATA_WIDTH,
      OFFSET_WIDTH      => OFFSET_WIDTH,
      EN_MASK           => EN_MASK
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,
      PAUSE_EDITING     => editor_pause,
      DATA_OUT          => editor_data_out,
      VLD               => editor_in_vld,
      DATA_IN           => editor_data_in,
      GET_NEW_PACEKT    => editor_next_packet,
      START_REPLACE     => editor_start,
      IN_OFFSET         => editor_in_offset,
      MASK              => editor_mask,
      NEW_DATA          => editor_new_data,
      SHIFT             => editor_shift,
      FLU_STATE         => flu_state,
      EOP_POS           => rx_eop_pos_editor,
      ENABLE_EDIT       => in_enable
   );
end architecture;
