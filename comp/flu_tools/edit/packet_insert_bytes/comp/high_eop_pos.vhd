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

entity HIGH_SOP_EOP is
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

      RX_INSERT_ENABLE  : in std_logic;
      FRAME_SATE        : in std_logic_vector(2 downto 0);
      PAC_SHIFTING      : in std_logic;
      RX_EDIT_ENABLE    : in std_logic;
      RX_NEW_DATA       : in std_logic_vector((4*8)-1 downto 0);
      RX_MASK           : in std_logic_vector(3 downto 0);
      RX_OFFSET         : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      --! Frame Link Unaligned input interface
      RX_DATA           : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS        : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP            : in std_logic;
      RX_EOP            : in std_logic;
      RX_SRC_RDY        : in std_logic;
      RX_DST_RDY        : out std_logic;

      TX_INSERT_ENABLE  : out std_logic;
      TX_EDIT_ENABLE    : out std_logic;
      TX_NEW_DATA       : out std_logic_vector((4*8)-1 downto 0);
      TX_MASK           : out std_logic_vector(3 downto 0);
      TX_EOP_NEXT_FRAME : out std_logic;
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

architecture full of HIGH_SOP_EOP is
   signal f_state          : std_logic_vector(1 downto 0);
   signal state_two        : std_logic;
   signal state_tree       : std_logic;
   signal state_two_tree   : std_logic;
   signal split            : std_logic;
   signal split_pipe       : std_logic;
   signal high_eop         : std_logic;
begin

   TX_OFFSET         <= RX_OFFSET;
   TX_DATA           <= RX_DATA;
   TX_SOP_POS        <= RX_SOP_POS;
   TX_EOP_POS        <= RX_EOP_POS;
   TX_SOP            <= RX_SOP and not split_pipe;
   TX_EOP            <= RX_EOP;
   TX_EDIT_ENABLE    <= RX_EDIT_ENABLE;
   TX_NEW_DATA       <= RX_NEW_DATA;
   TX_MASK           <= RX_MASK;
   TX_EOP_NEXT_FRAME <= split;
   TX_SRC_RDY        <= RX_SRC_RDY;
   TX_INSERT_ENABLE  <= RX_INSERT_ENABLE;
   RX_DST_RDY        <= TX_DST_RDY and not split;

   f_state           <= FRAME_SATE(1 downto 0);

   process(f_state, RX_INSERT_ENABLE)
   begin
      state_two <= '0';
      if(f_state = "10" and RX_INSERT_ENABLE = '1') then
         state_two <= '1';
      end if;
   end process;

   process(f_state, PAC_SHIFTING, RX_SRC_RDY)
   begin
      state_tree <= '0';
      if(f_state = "11" and PAC_SHIFTING = '1') then
         state_tree <= '1';
      end if;
   end process;

   state_two_tree <= state_two or state_tree;

   process(state_two_tree, RX_SRC_RDY, split_pipe, high_eop)
   begin
      split <= '0';
      if(RX_SRC_RDY = '1') then
         if(state_two_tree = '1' and split_pipe = '0' and high_eop = '1') then
            split <= '1';
         end if;
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            split_pipe  <= '0';
         elsif(TX_DST_RDY = '1') then
            split_pipe  <= split;
         end if;
      end if;
   end process;

   process(RX_EOP_POS(RX_EOP_POS'length-1 downto 2))
   begin
      high_eop <= '0';
      if(RX_EOP_POS(RX_EOP_POS'length-1 downto 2) = conv_std_logic_vector(15, RX_EOP_POS'length-2)) then
         high_eop <= '1';
      end if;
   end process;

end architecture;

