--
-- Copyright (C) 2016 CESNET
-- Author(s): Mário Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

entity FLU_SPLIT is
   generic(
      --! data width
      DATA_WIDTH 	      : integer := 512;
      --! sop_pos whidth (max value = log2(DATA_WIDTH/8))
      SOP_POS_WIDTH 	   : integer := 3;
      -- offset_width
      OFFSET_WIDTH      : integer := 10
   );
   port(
      CLK               : in std_logic;
      RESET             : in std_logic;

      RX_INSERT_ENABLE  : in std_logic;
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

      FRAME_SATE        : out std_logic_vector(2 downto 0);
      PAC_SHIFTING      : out std_logic;
      TX_INSERT_ENABLE  : out std_logic;
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

architecture full of FLU_SPLIT is
   constant sop_pos_num       : integer := 2**SOP_POS_WIDTH;
   constant sm_width          : integer := log2((DATA_WIDTH-(DATA_WIDTH/sop_pos_num))/8/4);
   constant num_block         : integer := ((DATA_WIDTH/8)/4)/sop_pos_num;

   signal mux_sop_in          : std_logic_vector(sm_width*sop_pos_num-1 downto 0);
   signal mux_sop_out         : std_logic_vector(sm_width-1 downto 0);

   signal cmp_sop_eop1        : std_logic_vector(47 downto 0);
   signal cmp_sop_eop2        : std_logic_vector(47 downto 0);
   signal cmp_sop_eop_up_in1  : std_logic_vector(47 downto 0);
   signal cmp_sop_eop_up_in2  : std_logic_vector(47 downto 0);

   signal cmp_sop_eop_up_out  : std_logic_vector(1 downto 0);
   signal cmp_sop_eop_out     : std_logic_vector(1 downto 0);

   signal sop_lees_eop        : std_logic;
   signal split               : std_logic;
   signal split_pipe          : std_logic;

   signal insert_start        : std_logic;
   signal insert_stop         : std_logic;
   signal inserting           : std_logic;
   signal inserting_pipe      : std_logic;

   signal tx_sop_out          : std_logic;
   signal tx_eop_out          : std_logic;
begin

   process(cmp_sop_eop_out(1), tx_sop_out, tx_eop_out)
   begin
      FRAME_SATE <= (others => '0');

      if(tx_sop_out = '0') then
         -- 0,1,x
         if(tx_eop_out = '1') then
            FRAME_SATE <= "011";
         end if;
      else
         -- 1,0,x
         if(tx_eop_out = '0') then
            FRAME_SATE <= "001";
         else
            -- 1,1, sop < eop
            if(cmp_sop_eop_out(1) = '1') then
               FRAME_SATE <= "010";
            else
               FRAME_SATE <= "100";
            end if;
         end if;
      end if;
   end process;

   PAC_SHIFTING      <= inserting_pipe;
   RX_DST_RDY        <= TX_DST_RDY and not split;
   TX_INSERT_ENABLE  <= RX_INSERT_ENABLE and RX_SRC_RDY and tx_sop_out;

   TX_OFFSET         <= RX_OFFSET;
   TX_EOP            <= tx_eop_out;
   TX_SOP            <= tx_sop_out;
   TX_DATA           <= RX_DATA;
   TX_SOP_POS        <= RX_SOP_POS;
   TX_EOP_POS        <= RX_EOP_POS;
   TX_SRC_RDY        <= RX_SRC_RDY;
   TX_EDIT_ENABLE    <= RX_EDIT_ENABLE;
   TX_NEW_DATA       <= RX_NEW_DATA;
   TX_MASK           <= RX_MASK;

   -- generate bytes index of sop_pos
   GEN_SOP_MUX_IN: for I in 0 to sop_pos_num-1 generate
      mux_sop_in(sm_width-1+I*sm_width downto I*sm_width) <= conv_std_logic_vector(num_block*I, sm_width);
   end generate;

   -- select index
   MUX_SOP_OFFSET: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => sm_width,
      MUX_WIDTH   => sop_pos_num
   )
   port map(
      DATA_IN     => mux_sop_in,
      SEL         => RX_SOP_POS,
      DATA_OUT    => mux_sop_out
   );

   -- compare sop_pos and add_eop_pos
   cmp_sop_eop_up_in1(mux_sop_out'length-1 downto 0)  <= mux_sop_out;
   cmp_sop_eop_up_in1(47 downto mux_sop_out'length)   <= (others => '0');
   cmp_sop_eop_up_in2(RX_EOP_POS'length-2 downto 0)   <= ('0' & RX_EOP_POS(RX_EOP_POS'length-1 downto 2)) + 1;
   cmp_sop_eop_up_in2(47 downto RX_EOP_POS'length-1)  <= (others => '0');

   --CMP_SOP_POS_UP_inst: entity work.CMP_DSP
   --generic map(
   --   DATA_WIDTH  => 48,
   --   REG_IN      => 0,
   --   REG_OUT     => 0
   --)
   --port map(
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => cmp_sop_eop_up_in1,
   --   B           => cmp_sop_eop_up_in2,
   --   CE_IN       => '1',
   --   CE_OUT      => '1',
   --   --! "00" when  A > B
   --   --! "10" when  A < B
   --   --! "11" when  A = B
   --   --! "01" undefined
   --   P           => cmp_sop_eop_up_out
   --);

   cmp_sop_eop_up_out <= "10" when cmp_sop_eop_up_in1 <= cmp_sop_eop_up_in2 else
                         "00";

   cmp_sop_eop1(mux_sop_out'length-1 downto 0)  <= mux_sop_out;
   cmp_sop_eop1(47 downto mux_sop_out'length)   <= (others => '0');
   cmp_sop_eop2(RX_EOP_POS'length-2 downto 0)   <= ('0' & RX_EOP_POS(RX_EOP_POS'length-1 downto 2));
   cmp_sop_eop2(47 downto RX_EOP_POS'length-1)  <= (others => '0');

   --CMP_EOP_SOP_inst: entity work.CMP_DSP
   --generic map(
   --   DATA_WIDTH  => 48,
   --   REG_IN      => 0,
   --   REG_OUT     => 0
   --)
   --port map(
   --   CLK         => CLK,
   --   RESET       => RESET,
   --   A           => cmp_sop_eop1,
   --   B           => cmp_sop_eop2,
   --   CE_IN       => '1',
   --   CE_OUT      => '1',
   --   --! "00" when  A > B
   --   --! "10" when  A < B
   --   --! "11" when  A = B
   --   --! "01" undefined
   --   P           => cmp_sop_eop_out
   --);

   cmp_sop_eop_out <= "10" when cmp_sop_eop1 <= cmp_sop_eop2 else
                      "00";

   process(cmp_sop_eop_out(1), cmp_sop_eop_up_out(1))
   begin
      sop_lees_eop <= '0';
      if(cmp_sop_eop_out(1) = '0' and cmp_sop_eop_up_out(1) = '0') then
         sop_lees_eop <= '1';
      end if;
   end process;


   insert_start  <= RX_SOP and RX_INSERT_ENABLE and RX_SRC_RDY;
   insert_stop   <= RX_EOP and RX_SRC_RDY;

   process(insert_start, insert_stop, inserting_pipe, cmp_sop_eop_out(1))
   begin
      inserting <= '0';
      if(inserting_pipe = '0') then
         if(insert_start = '1' and insert_stop = '0') then
            inserting <= '1';
         elsif(insert_start = '1' and insert_stop = '1' and cmp_sop_eop_out(1) = '0') then
            inserting <= '1';
         end if;
      else
         if(insert_start = '1' and insert_stop = '1') then
            inserting <= '1';
         elsif(insert_stop = '0') then
            inserting <= '1';
         end if;
      end if;
   end process;

   process(RX_SOP, RX_EOP, sop_lees_eop, RX_SRC_RDY, split_pipe, inserting_pipe)
   begin
      split <= '0';
      if(RX_SRC_RDY = '1') then
         if(RX_SOP = '1' and RX_EOP = '1' and sop_lees_eop = '0' and split_pipe = '0') then
            if(inserting_pipe = '1') then
               split <= '1';
            end if;
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

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            inserting_pipe <= '0';
         elsif(TX_DST_RDY = '1' and split = '0') then
            inserting_pipe <= inserting;
         end if;
      end if;
   end process;

   process(RX_SOP, split)
   begin
      if(split = '1') then
         tx_sop_out <= '0';
      else
         tx_sop_out <= RX_SOP;
      end if;
   end process;

   process(RX_EOP, split_pipe)
   begin
      if(split_pipe = '1') then
         tx_eop_out <= '0';
      else
         tx_eop_out <= RX_EOP;
      end if;
   end process;

end architecture;

