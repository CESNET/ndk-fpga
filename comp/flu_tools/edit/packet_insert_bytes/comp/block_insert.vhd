-- Copyright (C) 2015 CESNET
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

entity BLOCK_INSERT is
      generic(
      DATA_WIDTH 	   : integer := 512;
      -- offfset block - max 48 bits
      OFFSET_WIDTH   : integer := 10
   );
   port(
      CLK            : in std_logic;
      RESET          : in std_logic;

      -- offset of four bytes blocks
      OFFSET         : in std_logic_vector(OFFSET_WIDTH-1 downto 0);
      -- offset is valid
      OFFSET_VLD     : in std_logic;

      -- eop pos
      EOP_POS        : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      -- indicate end packet
      EOP            : in std_logic;

      -- input data
      DATA_IN        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      SRC_RDY        : in std_logic;

      -- output data
      DATA_OUT       : out std_logic_vector(DATA_WIDTH-1 downto 0);
      DST_RDY        : in std_logic;

      TX_EOP_POS     : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0)
   );
end entity;

architecture full of BLOCK_INSERT is
   constant num_blocks     : integer := (DATA_WIDTH/8)/4;
   constant log_block      : integer := log2(num_blocks);

   signal m1               : std_logic_vector(1 downto 0);
   signal m2               : std_logic_vector(1 downto 0);
   signal m2_pipe_mux      : std_logic_vector(1 downto 0);
   signal m1_pipe          : std_logic_vector(1 downto 0);
   signal m2_pipe          : std_logic_vector(1 downto 0);

   signal offset_conv      : std_logic_vector(num_blocks-1 downto 0);
   signal mux_offs_in      : std_logic_vector(3*num_blocks-1 downto 0);
   signal mux_offs_sel     : std_logic_vector(1 downto 0);
   signal mux_offs_out     : std_logic_vector(num_blocks-1 downto 0);
   signal mux_offs_out_pipe     : std_logic_vector(num_blocks-1 downto 0);

   signal mux_offs_end_in  : std_logic_vector(4*num_blocks-1 downto 0);
   signal mux_offs_end_out : std_logic_vector(num_blocks-1 downto 0);
   signal mux_offs_end_out_pipe : std_logic_vector(num_blocks-1 downto 0);
   signal sel_mux_end      : std_logic_vector(1 downto 0);

   signal eop_pos_conv     : std_logic_vector(num_blocks-1 downto 0);
   signal eop_pos_conv_pipe     : std_logic_vector(num_blocks-1 downto 0);

   signal tmp_and_out      : std_logic_vector(eop_pos_conv'length-1 downto 0);
   signal tmp_or_out       : std_logic_vector(eop_pos_conv'length-1 downto 0);

   signal pause            : std_logic;
   signal src_rdy_pipe     : std_logic;
   signal data_in_pipe     : std_logic_vector(DATA_WIDTH-1 downto 0);

   signal mux_eop_pos      : std_logic;
   signal eop_constant     : std_logic_vector(EOP_POS'length-1 downto 0);
   signal eop_pos_up       : std_logic_vector(EOP_POS'length-1 downto 0);

   signal eop_select_block :std_logic_vector(EOP_POS'length-1 downto EOP_POS'length-log_block);

   signal sop_sm_eop       : std_logic;
begin

   process(eop_select_block, OFFSET)
   begin
      sop_sm_eop <= '0';
      if(OFFSET < eop_select_block) then
         sop_sm_eop <= '1';
      end if;
   end process;

   pause <= DST_RDY and SRC_RDY;

   eop_constant <= conv_std_logic_vector(4, eop_constant'length);
   eop_pos_up <= EOP_POS + eop_constant;

   process(eop_pos_up, EOP_POS, mux_eop_pos)
   begin
      if(mux_eop_pos = '0') then
         TX_EOP_POS <= EOP_POS;
      else
         TX_EOP_POS <= eop_pos_up;
      end if;
   end process;

   process(m1, m2)
   begin
      mux_eop_pos <= '1';
      if((m1 = "00" or m1 = "01") and m2 = "00") then
         mux_eop_pos <= '0';
      end if;
   end process;

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            m1_pipe <= (others => '0');
            m2_pipe <= (others => '0');
         elsif(pause = '1') then
            m1_pipe <= m1;
            m2_pipe <= m2;
         end if;
      end if;
   end process;

   process(OFFSET_VLD, EOP, sop_sm_eop, m1_pipe, m2_pipe)
   begin
         m1 <= "00";
         m2 <= "00";
         if(m1_pipe = "00" and m2_pipe = "00") then
            if(OFFSET_VLD = '1') then
               -- 01x
               if(EOP = '0') then
                  m1 <= "01";
               -- 111
               elsif(sop_sm_eop = '1') then
                  m1 <= "01";
                  m2 <= "10";
               -- 110
               else
                  m1 <= "01";
               end if;
            end if;
         end if;

         if(m1_pipe = "01" and m2_pipe = "10") then
            -- x0
            if(OFFSET_VLD = '1') then
               -- 01
               if(EOP = '0') then
                  m1 <= "01";
               -- 11
               else
                  if(sop_sm_eop = '1') then
                     m1 <= "01";
                     m2 <= "10";
                  else
                     m1 <= "01";
                  end if;
               end if;
            end if;
         end if;

         if(m1_pipe = "01" and m2_pipe = "00") then
            if(OFFSET_VLD = '0') then
               -- 00
               if(EOP = '0') then
                  m1 <= "10";
               -- 10
               else
                  m2 <= "01";
               end if;
            -- 11
            else
               m1 <= "01";
               m2 <= "11";
            end if;
         end if;

         if(m1_pipe = "10" and m2_pipe = "00") then
            if(OFFSET_VLD = '0') then
               -- 00
               if(EOP = '1') then
                  m2 <= "01";
               else
                  m1 <= "10";
               end if;
            -- 11
            else
               m1 <= "01";
               m2 <= "11";
            end if;
         end if;

         if(m1_pipe = "01" and m2_pipe = "11") then
            if(OFFSET_VLD = '0') then
               -- 00
               if(EOP = '0') then
                  m1 <= "10";
               -- 10
               else
                  m2 <= "01";
               end if;
            -- 11
            else
               m1 <= "01";
               m2 <= "11";
            end if;
         end if;

         if(m2_pipe = "01") then
            -- x0
            if(OFFSET_VLD = '1') then
               -- 01
               if(EOP = '0') then
                  m1 <= "01";
               -- 11
               else
                  if(sop_sm_eop = '1') then
                     m1 <= "01";
                     m2 <= "10";
                  else
                     m1 <= "01";
                  end if;

               end if;
            end if;
         end if;
   end process;

   -- convert eop pos to control signol for muxs array
   eop_select_block <= eop_pos_up(EOP_POS'length-1 downto EOP_POS'length-log_block);
   process(eop_select_block)
   begin
      eop_pos_conv  <= (others => '0');
      eop_pos_conv(conv_integer(eop_select_block) downto 0) <= (others => '1');
   end process;

   -- begin and end packet
   AND_inst: entity work.ALU_DSP
   generic map(
      DATA_WIDTH  => eop_pos_conv'length,
      REG_IN      => 0,
      REG_OUT     => 0
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      A           => eop_pos_conv_pipe,
      B           => mux_offs_out_pipe,
      ALUMODE     => "0011",
      CE_IN       => '1',
      CE_OUT      => '1',
      CARRY_IN    => '0',
      CARRY_OUT   => open,
      P           => tmp_and_out
   );
   --tmp_and_out <= eop_pos_conv and mux_offs_out;

   -- end and begin packet
   OR_inst: entity work.ALU_DSP
   generic map(
      DATA_WIDTH => eop_pos_conv'length,
      REG_IN      => 0,
      REG_OUT     => 0
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      A           => eop_pos_conv_pipe,
      B           => mux_offs_out_pipe,
      ALUMODE     => "0100",
      CE_IN       => '1',
      CE_OUT      => '1',
      CARRY_IN    => '0',
      CARRY_OUT   => open,
      P           => tmp_or_out
   );
   --tmp_or_out <= eop_pos_conv or mux_offs_out;

   -- convert offset to control signol for mux array
   process(OFFSET)
      variable tmp : integer;
   begin
      tmp := conv_integer(OFFSET(log2(num_blocks)-1 downto 0));
      for i in num_blocks-1 downto 0 loop
         if (i < tmp ) then
            offset_conv(i) <= '0';
         else
            offset_conv(i) <= '1';
         end if;
      end loop;
   end process;

   -- switch between NULL, offset, FULL
   mux_offs_in(num_blocks-1 downto 0)              <= (others => '0');
   mux_offs_in(num_blocks*2-1 downto num_blocks)   <= offset_conv;
   mux_offs_in(num_blocks*3-1 downto num_blocks*2) <= (others => '1');
   mux_offs_sel                                    <= m1;
   MUX_OFFS_NULL_FULL_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => num_blocks,
      MUX_WIDTH   => 3
   )
   port map(
      DATA_IN     => mux_offs_in,
      SEL         => mux_offs_sel,
      DATA_OUT    => mux_offs_out
   );

   -- select control data when packet is on end or not
   mux_offs_end_in(num_blocks-1 downto 0)                <= mux_offs_out_pipe;
   mux_offs_end_in(num_blocks*2-1 downto num_blocks)     <= eop_pos_conv_pipe;
   mux_offs_end_in(num_blocks*3-1 downto num_blocks*2)   <= tmp_and_out;
   mux_offs_end_in(num_blocks*4-1 downto num_blocks*3)   <= tmp_or_out;
   sel_mux_end                                           <= m2_pipe_mux;
   MUX_OFFS_END_inst: entity work.GEN_MUX
   generic map(
      DATA_WIDTH  => num_blocks,
      MUX_WIDTH   => 4
   )
   port map(
      DATA_IN     => mux_offs_end_in,
      SEL         => sel_mux_end,
      DATA_OUT    => mux_offs_end_out
   );

   process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if(RESET = '1') then
            src_rdy_pipe <= '0';
            m2_pipe_mux <= (others => '0');
         elsif(DST_RDY = '1') then
           mux_offs_out_pipe <= mux_offs_out;
           m2_pipe_mux <= m2;
           eop_pos_conv_pipe <= eop_pos_conv;
           data_in_pipe <= DATA_IN;
           src_rdy_pipe <= SRC_RDY;
         end if;
      end if;
   end process;

   mux_offs_end_out_pipe <= mux_offs_end_out;

   -- insert block with muliplexers array
   DATA_SHIFTER_inst: entity work.DATA_SHIFTER
   generic map(
      DATA_WIDTH  => DATA_WIDTH,
      MEM_EN      => true,
      IN_PIPE     => false
   )
   port map(
      CLK         => CLK,
      RESET       => RESET,
      MUX_SELS    => mux_offs_end_out_pipe,
      DATA_IN     => data_in_pipe,
      DATA_OUT    => DATA_OUT,
      SRC_RDY     => src_rdy_pipe,
      DST_RDY     => DST_RDY
   );

end architecture;

