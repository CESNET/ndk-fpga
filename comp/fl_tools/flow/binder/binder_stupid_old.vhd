-- binder_stupid.vhd: FrameLink STUPID Binder architecture
-- Copyright (C) 2007 CESNET
-- Author(s): Jan Plešek <xplese01@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use work.math_pack.all;
use work.fl_binder_decl.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BINDER_STUPID is
   generic(
      INPUT_WIDTH    : integer;
      INPUT_COUNT    : integer;
      OUTPUT_WIDTH   : integer;
      FRAME_PARTS    : integer;
      QUEUE_CHOOSING : T_BINDER_QUEUE_POLICY := most_occupied
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- input FrameLink interface
      RX_SOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOP_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_EOF_N       : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_SRC_RDY_N   : in  std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DST_RDY_N   : out std_logic_vector(INPUT_COUNT-1 downto 0);
      RX_DATA        : in  std_logic_vector(INPUT_COUNT*INPUT_WIDTH-1
                                                                     downto 0);
      RX_REM         : in  std_logic_vector(INPUT_COUNT*log2(INPUT_WIDTH/8)-1
                                                                     downto 0);

      -- output FrameLink interface
      TX_SOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic;
      TX_DATA        : out std_logic_vector(OUTPUT_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(OUTPUT_WIDTH/8)-1 downto 0)
   );
end entity FL_BINDER_STUPID;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of FL_BINDER_STUPID is

   -- ------------------ Constants declaration --------------------------------
   constant STATUS_WIDTH         : integer := 4;
   constant ITEM_COUNT           : integer := 2048 / (OUTPUT_WIDTH / 8);
   -- set to cover situation, when memory is full of one-word frames
   constant FRAMECOUNTER_WIDTH   : integer := log2(ITEM_COUNT+1);

   -- ------------------ Signals declaration ----------------------------------
 --   signal clk       : std_logic;
 --   signal reset     : std_logic;

   signal hold_fl   : std_logic;
   signal num_fl    : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal my_shift  : std_logic_vector(INPUT_COUNT-1 downto 0);
   signal start_num : std_logic_vector(log2(INPUT_COUNT)-1 downto 0);


begin


   RX_DST_RDY_N <= not num_fl;
   TX_SRC_RDY_N <= '0';


   num_fl_proc  : process(hold_fl,my_shift)
   begin
      if hold_fl = '0' then
         num_fl <= my_shift;
      elsif my_shift = conv_std_logic_vector(0,INPUT_COUNT) then
         num_fl <= conv_std_logic_vector(0,INPUT_COUNT);
      end if;
   end process;


   hold_fl_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         gengen: for i in 0 to INPUT_COUNT-1 loop
            if hold_fl = '0' and my_shift(i) = '1' and RX_SOF_N(i) = '0' then
               hold_fl <= '1';
            elsif hold_fl = '1' and RX_EOF_N(i) = '0' and start_num = conv_std_logic_vector(i,log2(INPUT_COUNT)) then
               hold_fl <= '0';
            elsif not RX_SOF_N = conv_std_logic_vector(0,INPUT_COUNT) then
               hold_fl <= '0';
            end if;
         end loop;
      end if;
   end process;




   start_num_proc : process(hold_fl,my_shift)
   begin
      gengen: for i in 0 to INPUT_COUNT-1 loop
         if hold_fl = '0' and my_shift(i) = '1' and RX_SOF_N(i) = '0' then
            start_num <= conv_std_logic_vector(i,log2(INPUT_COUNT));
         end if;
      end loop;
   end process;



   my_shift_proc : process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            my_shift <= conv_std_logic_vector(1,INPUT_COUNT);
         elsif hold_fl = '0' then
             my_shift <= my_shift(INPUT_COUNT-2 downto 0) & my_shift(INPUT_COUNT-1);
         end if;
      end if;
   end process;

end architecture full;
