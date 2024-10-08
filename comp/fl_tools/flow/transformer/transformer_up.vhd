-- transformer_up.vhd: Implementation of UP architecture of FrameLink
-- Transformer component.
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Louda <sandin@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ------------------------------------------------------------------------
--                        Entity declaration
-- ------------------------------------------------------------------------
entity FL_TRANSFORMER_UP is
   generic(
      -- FrameLink data buses width
      -- only 8, 16, 32, 64 and 128 supported
      -- !! RX_DATA_WIDTH < TX_DATA_WIDTH !!
      RX_DATA_WIDTH  : integer;
      TX_DATA_WIDTH  : integer
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- RX interface
      RX_DATA        : in  std_logic_vector(RX_DATA_WIDTH-1 downto 0);
      RX_REM         : in  std_logic_vector(max(log2(RX_DATA_WIDTH/8)-1, 0) downto 0);
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      -- TX interface
      TX_DATA        : out std_logic_vector(TX_DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(TX_DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end entity FL_TRANSFORMER_UP;

-- ------------------------------------------------------------------------
--                      Architecture declaration
-- ------------------------------------------------------------------------
architecture full_up of FL_TRANSFORMER_UP is

   constant bytes_cnt   : integer := (TX_DATA_WIDTH/RX_DATA_WIDTH);

   signal data_strobe   : std_logic;
   signal dst_rdy       : std_logic;
   signal lblk          : std_logic;

   signal flag_sop      : std_logic;
   signal flag_sof      : std_logic;
   signal flag_run      : std_logic;

   signal act_byte      : std_logic_vector(log2(TX_DATA_WIDTH/RX_DATA_WIDTH) downto 0);

   signal reg_data      : std_logic_vector(TX_DATA_WIDTH-RX_DATA_WIDTH-1 downto 0) := (others => '0');

begin

   assert (RX_DATA_WIDTH < TX_DATA_WIDTH)
      report "FL_TRANSFORMER: Bad use of UP architecture - RX_DATA_WIDTH must be smaller than TX_DATA_WIDTH."
      severity error;

   -- output ports
   TX_EOP_N       <= RX_EOP_N or RX_SRC_RDY_N;
   TX_EOF_N       <= RX_EOF_N or RX_SRC_RDY_N;
   TX_SOP_N       <= not (lblk and ((not RX_SOP_N) or flag_sop));
   TX_SOF_N       <= not (lblk and ((not RX_SOF_N) or flag_sof));
   RX_DST_RDY_N   <= not dst_rdy;
   TX_SRC_RDY_N   <= not lblk;

   txrem_gt8_gen: if RX_DATA_WIDTH > 8 generate
      TX_REM <= conv_std_logic_vector((conv_integer(act_byte)-1)*RX_DATA_WIDTH/8
         + conv_integer(RX_REM), log2(TX_DATA_WIDTH/8))
         when (lblk = '1')
         else (others => '0');
   end generate txrem_gt8_gen;

   txrem8_gen: if RX_DATA_WIDTH = 8 generate
      TX_REM <= conv_std_logic_vector(conv_integer(act_byte-1), log2(TX_DATA_WIDTH/8));
   end generate txrem8_gen;

   data_strobe <= dst_rdy and (not RX_SRC_RDY_N);

   dst_rdy <= (not lblk) or (not TX_DST_RDY_N)
      when (flag_run = '1') or (lblk = '1')
      else not TX_DST_RDY_N;

   -- ---------------------------------------------------------------------
   --                   Main logic
   -- ---------------------------------------------------------------------

   lblk  <= '1'
      when ((RX_EOP_N = '0') or (conv_integer(act_byte) = bytes_cnt)) and (RX_SRC_RDY_N = '0')
      else '0';

   act_bytep: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            act_byte <= conv_std_logic_vector(1, log2(TX_DATA_WIDTH/RX_DATA_WIDTH)+1);
         else
            if ((TX_DST_RDY_N = '0') and (RX_SRC_RDY_N = '0')) then
               if (lblk = '1') then
                  act_byte <= conv_std_logic_vector(1, log2(TX_DATA_WIDTH/RX_DATA_WIDTH)+1);
               else
                  act_byte <= act_byte + 1;
               end if;
            end if;
         end if;
      end if;
   end process;

   -- output data shifting logic
   GEN_TX_DATA: for i in (TX_DATA_WIDTH/RX_DATA_WIDTH)-1 downto 0 generate
      process(reg_data, RX_DATA, lblk, act_byte)
      begin
         if (lblk = '1') then
            if (conv_integer(act_byte) = i+1) then
               TX_DATA((RX_DATA_WIDTH*(i+1))-1 downto RX_DATA_WIDTH*i) <= RX_DATA;
            elsif (i = (TX_DATA_WIDTH/RX_DATA_WIDTH)-1) then
               TX_DATA((RX_DATA_WIDTH*(i+1))-1 downto RX_DATA_WIDTH*i) <= (others => '0');
            else
               TX_DATA((RX_DATA_WIDTH*(i+1))-1 downto RX_DATA_WIDTH*i) <= reg_data((RX_DATA_WIDTH*(i+1))-1 downto RX_DATA_WIDTH*i);
            end if;
         else
            TX_DATA((RX_DATA_WIDTH*(i+1))-1 downto RX_DATA_WIDTH*i) <= (others => '0');
         end if;
      end process;
   end generate;

   -- ---------------------------------------------------------------------
   --                   Registers
   -- ---------------------------------------------------------------------

   flag_sopp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            flag_sop <= '0';
         else
            if (lblk = '1' and TX_DST_RDY_N = '0') then
               flag_sop <= '0';
            elsif (RX_SOP_N = '0' and RX_SRC_RDY_N = '0') then
               flag_sop <= '1';
            end if;
         end if;
      end if;
   end process;

   flag_sofp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            flag_sof <= '0';
         else
            if (lblk = '1' and TX_DST_RDY_N = '0') then
               flag_sof <= '0';
            elsif (RX_SOF_N = '0' and RX_SRC_RDY_N = '0') then
               flag_sof <= '1';
            end if;
         end if;
      end if;
   end process;

   flag_runp: process(RESET, CLK)
   begin
      if (CLK'event AND CLK = '1') then
         if (RESET = '1') then
            flag_run <= '0';
         else
            if (RX_EOF_N = '1' and RX_SRC_RDY_N = '0') then
               flag_run <= '0';
            elsif (RX_SOF_N = '0' AND RX_EOF_N = '0' AND RX_SRC_RDY_N = '0') then
               flag_run <= '0';
            elsif (RX_SOF_N = '0' and RX_SRC_RDY_N = '0') then
               flag_run <= '1';
            end if;
         end if;
      end if;
   end process;

   -- output data registers
   GEN_DATA:
   for i in 0 to (TX_DATA_WIDTH/RX_DATA_WIDTH)-2 generate
      process(CLK)
      begin
         if (CLK'event AND CLK = '1') then
            if ((data_strobe = '1') and (conv_integer(act_byte)-1 = i)) then
               reg_data(((i+1)*RX_DATA_WIDTH)-1 downto i*RX_DATA_WIDTH) <= RX_DATA;
            end if;
         end if;
      end process;
   end generate;

end architecture full_up;
