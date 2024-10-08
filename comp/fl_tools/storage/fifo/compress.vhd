-- compress.vhd: Frame Link protocol signals compressor
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

entity fl_compress is
   generic(
      WIRES : integer := 1 -- 1, 2, or 4
   );
   port(
      -- Common interface
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      -- Recieve interface
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : in  std_logic; -- Is input, because this comp does not
                                      -- perform flow control.
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;

      FL_JUICE       : out std_logic_vector(WIRES-1 downto 0);
         -- Compressed FL control signals

      FRAME_PART     : out std_logic
         -- Every cycle in '1' means one frame part
   );
end entity;


architecture full of fl_compress is
   signal sig_juice     : std_logic_vector(3 downto 0); -- output signal
   signal reg_first     : std_logic;   -- Is set to '1' after first frame ends
   signal sig_frame_part: std_logic;   -- output

begin
   sig_juice <= RX_SOF_N & RX_SOP_N & RX_EOF_N & RX_EOP_N; -- All signals

   -- Register to remember that first frame is gone
   reg_first_p : process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         if(RESET = '1') then
            reg_first <= '0';
         elsif(RX_EOF_N = '0' and RX_SRC_RDY_N = '0' and RX_DST_RDY_N = '0') then
            reg_first <= '1';
         end if;
      end if;
   end process;

   -- Each end of part except the last one is marked
   sig_frame_part <= (not RX_SRC_RDY_N) and
                     (not RX_DST_RDY_N) and
                     (not RX_EOP_N) and
                     (RX_EOF_N) and
                     (not reg_first);

   FL_JUICE    <= sig_juice(WIRES-1 downto 0);
   FRAME_PART  <= sig_frame_part;
end architecture full;

