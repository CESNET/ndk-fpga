--
-- fl_frame_spliter.vhd: Dividing Framelink into two parts
-- Copyright (C) 2006 CESNET
-- Author(s): Jan Kastil <xkasti00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use work.fl_pkg.all;
use work.fl_sim_oper.all;
-- library containing log2 function
use work.math_pack.all;

architecture full of frame_spliter is

signal Status         : std_logic;
signal Statusp         : std_logic;
signal Counter        : std_logic_vector(log2(FL_WIDTH_IN) downto 0);
signal CounterMin     : std_logic_vector(log2(FL_WIDTH_IN) downto 0);

signal RX1_SOP        : std_logic;
signal RX1_EOP        : std_logic;
signal RX1_EOF        : std_logic;
signal RX2_SOF        : std_logic;
signal RX2_EOF        : std_logic;
signal RX2_SOP        : std_logic;
signal RX2_EOP        : std_logic;
signal RX2_SRC        : std_logic;
signal RX2_DST        : std_logic;
signal RX1_SRC        : std_logic;
signal RX1_DST        : std_logic;
signal RX_DST         : std_logic;

signal RX_SOP_Nd        : std_logic;
signal RX_EOP_Nd        : std_logic;
signal RX_EOF_Nd        : std_logic;
signal RX_SOF_Nd        : std_logic;
signal RX_SRC_RDY_Nd        : std_logic;

signal Rovnost        : std_logic;
signal Start          : std_logic;

signal RX_DATAd             : std_logic_vector(FL_WIDTH_IN-1 downto 0);
signal RX_REMd              : std_logic_vector(log2(FL_WIDTH_IN/8)-1 downto 0);

begin
DReg_proc: process(fl_clk,fl_reset)
begin
   if(fl_reset='1') then
      RX_SOF_Nd <= '1';
      RX_EOF_Nd <= '1';
      RX_SOP_Nd <='1';
      RX_EOP_Nd <='1';
      RX_SRC_RDY_Nd <='1';
      RX_DATAd <= (others => '0');
      RX_REMd <= (others => '0');
      Statusp <= '0';
   elsif(fl_clk'event and fl_clk='1') then
     if (((RX_SRC_RDY_N='0') or (RX_SRC_RDY_Nd='0')) and (RX_DST='0')) then
      RX_SOP_Nd <= RX_SOP_N;
      RX_EOP_Nd <= RX_EOP_N;
      RX_EOF_Nd <= RX_EOF_N;
      RX_SOF_Nd <= RX_SOF_N;
      RX_SRC_RDY_Nd <= RX_SRC_RDY_N;
      RX_DATAd <= RX_DATA;
      RX_REMd <= RX_REM;
      Statusp <= Status;
    end if;
   end if;
end process;

Start_Proc: process(fl_clk,fl_reset,RX2_SOF)
begin
   if(fl_Reset = '1') then
      Start <='0';
   elsif(fl_clk'event and fl_clk='1') then
      if(Status='0') then Start<='0';
      end if;
      if((RX2_SOF = '0') and ((RX_SRC_RDY_Nd='0') and (RX_DST='0'))) then Start<='1';
      end if;
   end if;
end process;

EOF2_proc: process(Status,RX_EOF_Nd)
begin
   if(Status='1') then
      RX2_EOF <= RX_EOF_Nd;
   else
      RX2_EOF <= '1';
   end if;
end process;

Couner_Gen: process(Fl_Reset,Fl_clk)
begin
   if(Fl_Reset='1') then
      counter <= (others => '0');
   elsif(Fl_clk'event and Fl_clk='1') then
      if ((RX_EOF_Nd = '0') and ((RX_SRC_RDY_Nd='0') and (RX_DST='0'))) then
         Counter <= (others => '0');
      elsif ((RX_EOP_Nd = '0')  and ((RX_SRC_RDY_Nd='0') and (RX_DST='0'))) then
         counter <= counter+1;
         counterMin <= counter+2;
      end if;
   end if;
end process;


Stat_Gen : process(Fl_Reset,Fl_clk)
begin
   if(Fl_Reset = '1') then
      Status <= '0';
   elsif(Fl_clk'event and Fl_clk = '1') then
      if((RX_EOP_Nd = '0') and (Counter=(Split_Pos)) and (RX_EOF_Nd = '1') and ((RX_SRC_RDY_Nd='0') and (RX_DST='0')))  then
         Status <= '1';
      end if;
      if((RX_EOF_Nd = '0') and ((RX_SRC_RDY_Nd='0') and (RX_DST='0'))) then
         Status <='0';
      end if;
   end if;
end process;

-- EOF1_proc: process(Fl_clk)
-- begin
--    if(Fl_clk'event and Fl_clk='1') then
--       if(((Counter)=Split_Pos))  then
--         Rovnost<='0';
--       else
--          Rovnost<='1';
--       end if;
--    end if;
-- end process;

Rovnost  <= '0' when (Counter=Split_Pos)
	                   else ('1');

RX1_EOF <= (RX1_EOP or Rovnost or Status) and (RX_EOF_Nd or Status);

RX2_SOF <= (RX2_SOP or Start) or (RX_SRC_RDY_Nd);

SRC_RDY_proc: process(RX_SRC_RDY_Nd,Status)
begin
      if(Status='0') then
         RX1_SRC <=RX_SRC_RDY_Nd;
         RX2_SRC <= '1';
      else
         RX1_SRC <= '1';
         RX2_SRC <= RX_SRC_RDY_Nd;
      end if;
end process;


SOP_proc: process(RX_SOP_Nd,Status)
begin
      if(Status = '0') then
         RX1_SOP <= RX_SOP_Nd;
         RX2_SOP <= '1';
      else
         RX1_SOP <= '1';
         RX2_SOP <= RX_SOP_Nd;
      end if;
end process;

EOP_proc: process(RX_EOP_Nd,Status)
begin
      if(Status='0') then
         RX1_EOP <= RX_EOP_Nd;
         RX2_EOP <= '1';
      else
         RX1_EOP <= '1';
         RX2_EOP <= RX_EOP_Nd;
      end if;
end process;

RX_DST <= RX1_DST when Status = '0' else
                RX2_DST;

RX_DST_RDY_N <= RX_DST;

FL_TRASFORMER_OUT1: entity work.FL_TRANSFORMER
   generic map (
      RX_DATA_WIDTH=>FL_WIDTH_IN,
      TX_DATA_WIDTH=>FL_WIDTH_OUT1
   )
   port map (
      CLK => FL_CLK,
      RESET=> FL_RESET,

      RX_DATA=>RX_DATAd,
      RX_REM=>RX_REMd,
      RX_SOF_N=>RX_SOF_Nd,
      RX_EOF_N=>RX1_EOF,
      RX_SOP_N=>RX1_SOP,
      RX_EOP_N=>RX1_EOP,
      RX_SRC_RDY_N=>RX1_SRC,
      RX_DST_RDY_N=>RX1_DST,

      TX_DATA=>TX_DATA_OUT1,
      TX_REM=>TX_REM_OUT1,
      TX_SOF_N=>TX_SOF_N_OUT1,
      TX_EOF_N=>TX_EOF_N_OUT1,
      TX_SOP_N=>TX_SOP_N_OUT1,
      TX_EOP_N=>TX_EOP_N_OUT1,
      TX_SRC_RDY_N=>TX_SRC_RDY_N_OUT1,
      TX_DST_RDY_N=>TX_DST_RDY_N_OUT1
   );

FL_TRASFORMER_OUT2: entity work.FL_TRANSFORMER
   generic map (
      RX_DATA_WIDTH=>FL_WIDTH_IN,
      TX_DATA_WIDTH=>FL_WIDTH_OUT2
   )
   port map (
      CLK => FL_CLK,
      RESET=> FL_RESET,

      RX_DATA=>RX_DATAd,
      RX_REM=>RX_REMd,
      RX_SOF_N=>RX2_SOF,
      RX_EOF_N=>RX2_EOF,
      RX_SOP_N=>RX2_SOP,
      RX_EOP_N=>RX2_EOP,
      RX_SRC_RDY_N=>RX2_SRC,
      RX_DST_RDY_N=>RX2_DST,

      TX_DATA=>TX_DATA_OUT2,
      TX_REM=>TX_REM_OUT2,
      TX_SOF_N=>TX_SOF_N_OUT2,
      TX_EOF_N=>TX_EOF_N_OUT2,
      TX_SOP_N=>TX_SOP_N_OUT2,
      TX_EOP_N=>TX_EOP_N_OUT2,
      TX_SRC_RDY_N=>TX_SRC_RDY_N_OUT2,
      TX_DST_RDY_N=>TX_DST_RDY_N_OUT2
   );
end architecture full;
