-- decompress.vhd: Frame Link protocol signals decompressor
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

entity fl_decompress is
   generic(
      WIRES : integer := 1;   -- 1, 2, or 4
      PARTS : integer := 0    -- 0 - autodetect; 1,2,3 - Given value
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Transmit interface
      TX_SRC_RDY_N   : in  std_logic;
      TX_DST_RDY_N   : in  std_logic; -- Is input, because this comp does not
                                      -- perform flow control.
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;

      FL_JUICE       : in  std_logic_vector(WIRES-1 downto 0);
         -- Compressed FL control signals

      DISCARD        : in  std_logic;  -- Next item is SOF & SOP
      FRAME_PART     : in  std_logic
         -- Every cycle in '1' means one frame part
   );
end entity fl_decompress;

architecture full of fl_decompress is

signal reg_got2   : std_logic;   -- Is set to 1 if frames have 2 or 3 parts
signal reg_got3   : std_logic;   -- Is set to 1 if frames have 3 parts

signal reg_sop_n  : std_logic;   -- Registering EOP gives us SOP
signal reg_sof_n  : std_logic;   -- Registering EOF gives us SOF
signal sig_eof_n  : std_logic;   -- Computed value of control signal

signal reg_a2     : std_logic;
signal reg_a1     : std_logic;   -- Keep track of current frame

begin

-- This register is set to 1 if frame has two or three parts
got2_auto : if PARTS = 0 generate
   reg_got2_p: process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         if(RESET = '1') then
            reg_got2 <= '0';
         elsif(FRAME_PART = '1') then
            reg_got2 <= '1';
         end if;
      end if;
   end process;
end generate;
got2_1 : if PARTS = 1 generate
   reg_got2 <= '0';
end generate;
got2_23 : if PARTS > 1 generate
   reg_got2 <= '1';
end generate;

-- This register is set to 1 if frame has three parts
got3_auto : if PARTS = 0 generate
   reg_got3_p: process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         if(RESET = '1') then
            reg_got3 <= '0';
         elsif(FRAME_PART = '1' and reg_got2 = '1') then
            reg_got3 <= '1';
         end if;
      end if;
   end process;
end generate;
got3_12 : if PARTS = 1 or PARTS = 2 generate
   reg_got3 <= '0';
end generate;
got3_3 : if PARTS = 3 generate
   reg_got3 <= '1';
end generate;

-- Registering EOP_N (with respect to RDY signals) gives SOP_N
reg_sop_n_p: process(CLK)
begin
   if(CLK'event and CLK = '1') then
      if(RESET='1' or DISCARD='1') then
         reg_sop_n <= '0';
      elsif(TX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
         reg_sop_n <= FL_JUICE(0);
      end if;
   end if;
end process;

-- Registering EOF_N (with respect to RDY signals) gives SOF_N
reg_sof_n_p: process(CLK)
begin
   if(CLK'event and CLK = '1') then
      if(RESET='1' or DISCARD='1') then
         reg_sof_n <= '0';
      elsif(TX_DST_RDY_N = '0' and TX_SRC_RDY_N = '0') then
         reg_sof_n <= sig_eof_n;
      end if;
   end if;
end process;

-- This register is set to 1 when output frame ends first part and to 0 when output frame ends
proc_reg_a1: process(CLK)
begin
   if(CLK'event and CLK = '1') then
      if(RESET = '1' or DISCARD='1') then
         reg_a1 <= '0';
      elsif(TX_SRC_RDY_N = '0' and TX_DST_RDY_N = '0' and
         ((FL_JUICE(0) = '0' and reg_a1 = '0') or sig_eof_n = '0')) then
         reg_a1 <= not reg_a1;
      end if;
   end if;
end process;

-- This register is set to 1 when output frame ends second part and to 0 when output frame ends
proc_reg_a2 : process(CLK)
begin
   if(CLK'event and CLK = '1') then
      if(RESET = '1' or DISCARD='1') then
         reg_a2 <= '0';
      elsif(TX_SRC_RDY_N = '0' and TX_DST_RDY_N='0' and
         ((FL_JUICE(0)='0' and reg_a1='1' and reg_a2='0') or sig_eof_n='0')) then
         reg_a2 <= not reg_a2;
      end if;
   end if;
end process;

TX_EOP_N <= FL_JUICE(0);
TX_EOF_N <= sig_eof_n;

wire1n_cond : if(WIRES > 1) generate
   sig_eof_n <= FL_JUICE(1);
end generate;

wire1_cond : if(WIRES = 1) generate
   sig_eof_n <=  not(not FL_JUICE(0) and ((not reg_got2) or
                                  (reg_a1 and not reg_got3) or
                                  (reg_a1 and reg_a2)));
end generate;

wire4n_cond : if(WIRES < 4) generate
   TX_SOP_N <= reg_sop_n;
   TX_SOF_N <= reg_sof_n;
end generate;

wire4_cond : if(WIRES = 4) generate
   TX_SOP_N <= FL_JUICE(2);
   TX_SOF_N <= FL_JUICE(3);
end generate;

end architecture full;

