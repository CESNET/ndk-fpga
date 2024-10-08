-- Copyright (C) 2016 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity INSERT_OFFSET is
   generic(
      --! data width
      DATA_WIDTH 	      : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	   : integer := 3;
      --! select four bytes block of packet
      OFFSET_WIDTH      : integer := 10
   );
   port(
      CLK               : in std_logic;
      RESET             : in std_logic;

      --! enable insert data
      EN_INSERT         : in std_logic;
      OFFSET            : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      RX_EOP_NEXT_FRAME : in std_logic;
      RX_EDIT_ENABLE    : in std_logic;
      RX_NEW_DATA       : in std_logic_vector((4*8)-1 downto 0);
      RX_MASK           : in std_logic_vector(3 downto 0);
      --! Frame Link Unaligned input interface
      RX_DATA           : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS        : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP            : in std_logic;
      RX_EOP            : in std_logic;
      RX_SRC_RDY        : in std_logic;
      RX_DST_RDY        : out std_logic;

      BLOCK_INSER_OFFSET : out std_logic_vector(OFFSET_WIDTH-1 downto 0);
      BLOCK_INSER_BEGIN  : out std_logic;
      TX_EOP_NEXT_FRAME : out std_logic;
      TX_FLU_STATE      : out std_logic_vector(2 downto 0);
      TX_EDIT_ENABLE    : out std_logic;
      TX_NEW_DATA       : out std_logic_vector((4*8)-1 downto 0);
      TX_MASK           : out std_logic_vector(3 downto 0);
      TX_OFFSET         : out std_logic_vector(OFFSET_WIDTH-1 downto 0);
      --! Frame Link Unaligned output interface
      TX_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS        : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS        : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP            : out std_logic;
      TX_EOP            : out std_logic;
      TX_INSERT         : out std_logic;
      TX_SRC_RDY        : out std_logic;
      TX_DST_RDY        : in std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of INSERT_OFFSET is
   constant sop_pos_num             : integer := 2**SOP_POS_WIDTH;
	constant out_pipe_width          : integer := 1+1+SOP_POS_WIDTH+log2(DATA_WIDTH/8);
   constant num_bytes               : integer := DATA_WIDTH/8;
   constant num_blocks              : integer := num_bytes/4;
   signal zeros                     : std_logic_vector(511 downto 0);

   signal editor_pause              : std_logic;
   signal editor_data_out           : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal editor_in_vld             : std_logic;
   signal editor_data_in            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal editor_in_offset          : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal editor_next_packet        : std_logic;
   signal split_flu                 : std_logic;
   signal split_flu_reg             : std_logic;
   signal in_enable                 : std_logic;
   signal in_enable_zero            : std_logic;
   signal editor_start              : std_logic;

   signal enable_editor             : std_logic;
   signal offset_in_editor          : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal offset_editor             : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal rx_sop_pos_editor         : std_logic_vector(RX_SOP_POS'range);
   signal rx_eop_pos_editor         : std_logic_vector(RX_EOP_POS'range);
   signal data_in_editor            : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal sop_editor                : std_logic;
   signal eop_editor                : std_logic;
   signal src_rdy_editor            : std_logic;
   signal rx_eop_next_frame_editor  : std_logic;
   signal rx_edit_enable_editor     : std_logic;
   signal rx_new_data_editor        : std_logic_vector((8*4)-1 downto 0);
   signal rx_mask_editor            : std_logic_vector(3 downto 0);

   signal rx_eop_pos_pipe           : std_logic_vector(RX_EOP_POS'range);
   signal rx_sop_pos_pipe           : std_logic_vector(RX_SOP_POS'range);
   signal src_rdy_pipe              : std_logic;
   signal eop_pipe                  : std_logic;
   signal sop_pipe                  : std_logic;
   signal tx_dst_rdy_editor         : std_logic;
   signal zero_offset               : std_logic;
   signal editor_low_offset         : std_logic;
   signal rx_eop_next_frame_pipe    : std_logic;
   signal rx_edit_enable_pipe       : std_logic;
   signal rx_new_data_pipe          : std_logic_vector((8*4)-1 downto 0);
   signal rx_offset_pipe            : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal rx_mask_pipe              : std_logic_vector(3 downto 0);

   signal rx_eop_pos_pipe2          : std_logic_vector(RX_EOP_POS'range);
   signal rx_sop_pos_pipe2          : std_logic_vector(RX_SOP_POS'range);
   signal src_rdy_pipe2             : std_logic;
   signal eop_pipe2                 : std_logic;
   signal sop_pipe2                 : std_logic;
   signal rx_frame_state_pipe2      : std_logic_vector(2 downto 0);
   signal rx_eop_next_frame_pipe2   : std_logic;
   signal rx_edit_enable_pipe2      : std_logic;
   signal rx_new_data_pipe2         : std_logic_vector((8*4)-1 downto 0);
   signal rx_mask_pipe2             : std_logic_vector(3 downto 0);
   signal rx_offset_pipe2           : std_logic_vector(OFFSET_WIDTH-1 downto 0);

   signal mux_sop_in                : std_logic_vector(5*sop_pos_num-1 downto 0);
   signal mux_sop_sel               : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal mux_sop_out               : std_logic_vector(5-1 downto 0);

   signal add_in1                   : std_logic_vector(47 downto 0);
   signal add_in2                   : std_logic_vector(47 downto 0);
   signal add_out                   : std_logic_vector(47 downto 0);

   signal offset_sub_in1            : std_logic_vector(47 downto 0);
   signal offset_sub_in2            : std_logic_vector(47 downto 0);
   signal offset_sub_out            : std_logic_vector(47 downto 0);
   signal offset_alu_pipe_out       : std_logic_vector(OFFSET_WIDTH-1 downto 0);

   signal big_offset                : std_logic;
   signal big_offset_pipe           : std_logic;

   signal in_enable_next            : std_logic;
   signal split_flu_first           : std_logic;

   signal editor_insert_offset      : std_logic_vector(OFFSET_WIDTH-1 downto 0);
   signal editor_insert_enable      : std_logic;

   signal flu_state           : std_logic_vector(2 downto 0);
   signal flu_state_pipe      : std_logic_vector(2 downto 0);
   signal cmp_eop_sop_insop   : std_logic_vector(RX_EOP_POS'range);
   signal cmp_eop_sop         : std_logic;
   signal insert_pipe         : std_logic;
   signal insert_pipe2        : std_logic;

begin
   zeros <= (others => '0');

   -- input pipe
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            enable_editor            <= '0';
            src_rdy_pipe             <= '0';
            src_rdy_pipe2            <= '0';
            src_rdy_editor           <= '0';
            big_offset_pipe          <= '0';
            rx_eop_next_frame_editor <= '0';
            rx_eop_next_frame_pipe   <= '0';
            rx_eop_next_frame_pipe2  <= '0';
            eop_editor               <= '0';
            eop_pipe2                <= '0';
         else
            if(tx_dst_rdy_editor = '1') then
               rx_eop_next_frame_editor   <= RX_EOP_NEXT_FRAME;
               enable_editor              <= EN_INSERT;
               offset_in_editor           <= OFFSET;
               rx_sop_pos_editor          <= RX_SOP_POS;
               rx_eop_pos_editor          <= RX_EOP_POS;
               data_in_editor             <= RX_DATA;
               sop_editor                 <= RX_SOP;
               eop_editor                 <= RX_EOP;
               src_rdy_editor             <= RX_SRC_RDY;
               rx_edit_enable_editor      <= RX_EDIT_ENABLE;
               rx_new_data_editor         <= RX_NEW_DATA;
               rx_mask_editor             <= RX_MASK;
            end if;

            if(TX_DST_RDY = '1') then
               rx_eop_next_frame_pipe     <= rx_eop_next_frame_editor;
               rx_eop_pos_pipe            <= rx_eop_pos_editor;
               rx_sop_pos_pipe            <= rx_sop_pos_editor;
               src_rdy_pipe               <= src_rdy_editor;
               rx_edit_enable_pipe        <= rx_edit_enable_editor;
               rx_new_data_pipe           <= rx_new_data_editor;
               rx_mask_pipe               <= rx_mask_editor;
               rx_offset_pipe             <= offset_in_editor;
               big_offset_pipe            <= big_offset;
               insert_pipe                <= enable_editor;

               rx_eop_pos_pipe2           <= rx_eop_pos_pipe;
               rx_sop_pos_pipe2           <= rx_sop_pos_pipe;
               rx_eop_next_frame_pipe2    <= rx_eop_next_frame_pipe;
               src_rdy_pipe2              <= src_rdy_pipe;
               eop_pipe2                  <= eop_pipe;
               sop_pipe2                  <= sop_pipe;
               rx_edit_enable_pipe2       <= rx_edit_enable_pipe;
               rx_new_data_pipe2          <= rx_new_data_pipe;
               rx_mask_pipe2              <= rx_mask_pipe;
               rx_offset_pipe2            <= rx_offset_pipe;
               flu_state_pipe             <= flu_state;
               insert_pipe2               <= insert_pipe;
            end if;
         end if;
      end if;
   end process;

   BLOCK_INSER_OFFSET   <= editor_insert_offset;
   BLOCK_INSER_BEGIN    <= editor_insert_enable;

   TX_INSERT            <= insert_pipe2;
   TX_EOP_NEXT_FRAME    <= rx_eop_next_frame_pipe2;
   TX_DATA              <= editor_data_out;
   TX_SOP_POS           <= rx_sop_pos_pipe2;
   TX_EOP_POS           <= rx_eop_pos_pipe2;
   TX_EOP               <= eop_pipe2;
   TX_SOP               <= sop_pipe2;
   TX_SRC_RDY           <= src_rdy_pipe2;
   TX_EDIT_ENABLE       <= rx_edit_enable_pipe2;
   TX_NEW_DATA          <= rx_new_data_pipe2;
   TX_MASK              <= rx_mask_pipe2;
   TX_OFFSET            <= rx_offset_pipe2;
   RX_DST_RDY           <= tx_dst_rdy_editor;
   TX_FLU_STATE         <= flu_state_pipe;

   cmp_eop_sop_insop <= rx_sop_pos_pipe & zeros(RX_EOP_POS'length-SOP_POS_WIDTH-1 downto 0);
   cmp_eop_sop <= '1' when rx_eop_pos_pipe > cmp_eop_sop_insop else '0';

   flu_state <= "000" when eop_pipe = '0' and sop_pipe = '0' else
                "001" when eop_pipe = '1' and sop_pipe = '0' else
                "010" when eop_pipe = '0' and sop_pipe = '1' else
                "011" when eop_pipe = '1' and sop_pipe = '1' and cmp_eop_sop = '1' else
                "100";


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
   offset_editor  <= add_out(OFFSET_WIDTH-1 downto 0);

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

   in_enable_next <= RX_SRC_RDY and (not RX_SOP or not EN_INSERT);

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
         if(RESET = '1') then
            eop_pipe <= '0';
         elsif(TX_DST_RDY = '1') then
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
   --OFFSET_ALU: entity work.ALU_DSP
   --generic map(
   --   DATA_WIDTH  => 48,
   --   REG_IN      => 0,
   --   REG_OUT     => 1
   --)
   --port map (
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => offset_sub_in1,
   --   B           => offset_sub_in2,
   --   CE_IN       => '1',
   --   CE_OUT      => TX_DST_RDY,
   --   ALUMODE     => "0001",
   --   CARRY_IN    => '0',
   --   CARRY_OUT   => open,
   --   P           => offset_sub_out
   --);

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(TX_DST_RDY = '1') then
            offset_sub_out <= offset_sub_in1 - offset_sub_in2;
         end if;
      end if;
   end process;

   offset_alu_pipe_out <= offset_sub_out(OFFSET_WIDTH-1 downto 0);
   process(offset_editor, offset_alu_pipe_out, big_offset_pipe)
   begin
      if(big_offset_pipe = '1') then
         editor_in_offset <= offset_alu_pipe_out;
      else
         editor_in_offset <= offset_editor;
      end if;
   end process;

   -- alu for offset
   editor_pause         <= TX_DST_RDY;
   editor_in_vld        <= src_rdy_editor;
   editor_data_in       <= data_in_editor;
   OFFSET_CONTROL_inst : entity work.OFFSET_CONTROL
   generic map (
      DATA_WIDTH        => DATA_WIDTH,
      OFFSET_WIDTH      => OFFSET_WIDTH
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,

      PAUSE_EDITING     => editor_pause,

      DATA_OUT             => editor_data_out,
      BLOCK_INSER_OFFSET   => editor_insert_offset,
      BLOCK_INSER_BEGIN    => editor_insert_enable,

      VLD               => editor_in_vld,
      DATA_IN           => editor_data_in,
      START_REPLACE     => editor_start,
      IN_OFFSET         => editor_in_offset,
      GET_NEW_PACEKT    => editor_next_packet,
      FLU_STATE         => flu_state,
      EOP_POS           => rx_eop_pos_editor,
      ENABLE_EDIT       => in_enable
   );

end architecture;
