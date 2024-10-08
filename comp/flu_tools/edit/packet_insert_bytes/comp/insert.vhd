-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
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

entity INSERT is
   generic(
      --! data width
      DATA_WIDTH 	      : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	   : integer := 3;
      --! offset width
      OFFSET_WIDTH      : integer := 10
   );
   port(
      CLK               : in std_logic;
      RESET             : in std_logic;

      BLOCK_INSER_OFFSET : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      BLOCK_INSER_BEGIN : in std_logic;
      EOP_NEXT_FRAME    : in std_logic;
      FLU_STATE         : in std_logic_vector(2 downto 0);
      RX_EDIT_ENABLE    : in std_logic;
      RX_NEW_DATA       : in std_logic_vector((4*8)-1 downto 0);
      RX_MASK           : in std_logic_vector(3 downto 0);
      RX_OFFSET         : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      RX_INSERT         : in std_logic;
      --! Frame Link Unaligned input interface
      RX_DATA           : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS        : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP            : in std_logic;
      RX_EOP            : in std_logic;
      RX_SRC_RDY        : in std_logic;
      RX_DST_RDY        : out std_logic;

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
      TX_SRC_RDY        : out std_logic;
      TX_DST_RDY        : in std_logic
  );
end entity;

architecture full of INSERT is
  signal zeros             : std_logic_vector(511 downto 0);
  signal mux_control_pipe  : std_logic;
  signal mux_control       : std_logic;

  signal tx_src_rdy_p      : std_logic;
  signal mux_eop           : std_logic;
  signal mux_sop           : std_logic;

  signal block_eop_pos     : std_logic_vector(RX_EOP_POS'length-1 downto 0);
  signal block_insert_eop  : std_logic;

  signal insert_begin_mem_pipe  : std_logic;
  signal insert_begin_mem       : std_logic;
  signal insert_begin_mem_rst   : std_logic;

  signal cmp_eop_offset1        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
  signal cmp_eop_offset2        : std_logic_vector(OFFSET_WIDTH-1 downto 0);
  signal cmp_eop_offset         : std_logic;
  signal big_eop                : std_logic;
  signal BLOCK_INSER_BEGIN_tmp  : std_logic;
  signal stop_next_eop          : std_logic;

  signal TX_EDIT_ENABLE_pipe    : std_logic;
  signal TX_NEW_DATA_pipe       : std_logic_vector((4*8)-1 downto 0);
  signal TX_MASK_pipe           : std_logic_vector(3 downto 0);
  signal TX_OFFSET_pipe         : std_logic_vector(OFFSET_WIDTH-1 downto 0);
  signal TX_SOP_POS_pipe        : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
  signal TX_EOP_POS_pipe        : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
  signal TX_SOP_pipe            : std_logic;
  signal TX_EOP_pipe            : std_logic;
  signal TX_SRC_RDY_pipe        : std_logic;

  signal cmp_out                : std_logic_vector(1 downto 0);
begin

   zeros <= (others => '0');

   -- compare EOP_POS and input offset
   cmp_eop_offset1 <= zeros(OFFSET_WIDTH-RX_EOP_POS'LENGTH-1+2 downto 0) & RX_EOP_POS(RX_EOP_POS'LENGTH-1 downto 2);
   cmp_eop_offset2 <= BLOCK_INSER_OFFSET;

   --dsp_cpm_i : entity work.CMP_DSP
   --generic map (
   --   DATA_WIDTH  => cmp_eop_offset1'LENGTH,
   --   REG_IN      => 0,
   --   REG_OUT     => 0
   --)
   --port map(
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => cmp_eop_offset1,
   --   B           => cmp_eop_offset2,
   --   CE_IN       => '1',
   --   CE_OUT      => '1',
   --   --! "00" when  A > B
   --   --! "10" when  A < B
   --   --! "11" when  A = B
   --   P           => cmp_out
   --);

   cmp_eop_offset  <= '1' when cmp_eop_offset1 < cmp_eop_offset2 else --cmp_out = "10" else
                      '0';
   big_eop <= '0' when cmp_eop_offset = '1' and (FLU_STATE = "001" or FLU_STATE = "011") else
              '1';

   -- control memory for start inserting
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            insert_begin_mem_rst <= '1';
            insert_begin_mem_pipe <= '0';
         elsif(TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
            insert_begin_mem_pipe <= insert_begin_mem;

            insert_begin_mem_rst <= '0';
            if(FLU_STATE = "001" or FLU_STATE = "011") then
               insert_begin_mem_rst <= '1';
            end if;
            if (FLU_STATE = "100" and ((cmp_eop_offset = '0' and BLOCK_INSER_BEGIN = '1') or
                                       (insert_begin_mem_pipe = '1' and BLOCK_INSER_BEGIN = '0')
                                      )
               ) then
               insert_begin_mem_rst <= '1';
            end if;
         end if;
      end if;
   end process;

   -- remember start inserting for packet
   process(BLOCK_INSER_BEGIN, insert_begin_mem_rst, insert_begin_mem_pipe)
   begin
      insert_begin_mem <= insert_begin_mem_pipe;
      if(insert_begin_mem_rst = '1') then
         insert_begin_mem <= '0';
      end if;
      if(BLOCK_INSER_BEGIN = '1') then
         insert_begin_mem <= '1';
      end if;
   end process;

   -- stop generate eop next cycle when packet is not editing
   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            stop_next_eop <= '0';
         elsif(TX_DST_RDY = '1' and RX_SRC_RDY = '1') then
            stop_next_eop <= '0';
            if(EOP_NEXT_FRAME = '1' and insert_begin_mem = '0') then
               stop_next_eop <= '1';
            end if;
         end if;
      end if;
   end process;

   mux_control <= EOP_NEXT_FRAME and insert_begin_mem;

   BLOCK_INSER_BEGIN_tmp <= BLOCK_INSER_BEGIN and big_eop;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            mux_control_pipe  <= '0';
         elsif(TX_DST_RDY = '1') then
            mux_control_pipe  <= mux_control;
         end if;
      end if;
   end process;

   tx_src_rdy_p <= RX_SRC_RDY;

   process(mux_control_pipe, RX_EOP_POS(1 downto 0), block_eop_pos)
   begin
      if(mux_control_pipe = '1') then
         TX_EOP_POS_pipe(TX_EOP_POS'length-1 downto 2) <= (others => '0');
         TX_EOP_POS_pipe(1 downto 0) <= RX_EOP_POS(1 downto 0);
      else
         TX_EOP_POS_pipe <= block_eop_pos;
      end if;
   end process;

   RX_DST_RDY          <= TX_DST_RDY;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            TX_SRC_RDY <= '0';
         elsif(TX_DST_RDY = '1') then
            TX_SRC_RDY     <= TX_SRC_RDY_pipe;
            TX_SOP_POS     <= TX_SOP_POS_pipe;
            TX_EOP         <= TX_EOP_pipe;
            TX_SOP         <= TX_SOP_pipe;
            TX_EDIT_ENABLE <= TX_EDIT_ENABLE_pipe;
            TX_NEW_DATA    <= TX_NEW_DATA_pipe;
            TX_MASK        <= TX_MASK_pipe;
            TX_OFFSET      <= TX_OFFSET_pipe;
            TX_EOP_POS     <= TX_EOP_POS_pipe;
         end if;
      end if;
   end process;

   TX_SRC_RDY_pipe     <= tx_src_rdy_p and not stop_next_eop;
   TX_SOP_POS_pipe     <= RX_SOP_POS;
   TX_EOP_pipe         <= block_insert_eop;
   TX_SOP_pipe         <= mux_sop;
   TX_EDIT_ENABLE_pipe <= RX_EDIT_ENABLE;
   TX_NEW_DATA_pipe    <= RX_NEW_DATA;
   TX_MASK_pipe        <= RX_MASK;
   TX_OFFSET_pipe      <= RX_OFFSET;

   process(RX_EOP, mux_control)
   begin
      if(mux_control = '0') then
         mux_eop <= RX_EOP;
      else
         mux_eop <= '0';
      end if;
   end process;

   process(RX_SOP, mux_control_pipe)
   begin
      if(mux_control_pipe = '0') then
         mux_sop <= RX_SOP;
      else
         mux_sop <= '0';
      end if;
   end process;

   block_insert_eop <= mux_eop and not stop_next_eop;
   BLOCK_INSERT_inst : entity work.BLOCK_INSERT
   generic map(
      DATA_WIDTH     => DATA_WIDTH,
      OFFSET_WIDTH   => OFFSET_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,
      OFFSET         => BLOCK_INSER_OFFSET,
      OFFSET_VLD     => BLOCK_INSER_BEGIN_tmp,
      EOP_POS        => RX_EOP_POS,
      EOP            => block_insert_eop,
      DATA_IN        => RX_DATA,
      SRC_RDY        => tx_src_rdy_p,
      DATA_OUT       => TX_DATA,
      DST_RDY        => TX_DST_RDY,
      TX_EOP_POS     => block_eop_pos
   );

end architecture;

