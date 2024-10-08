--
-- decoder_tb.vhd: Testbench
-- Copyright (C) 2003 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

   constant TEST_HEADER : boolean := true;
   constant TEST_FOOTER : boolean := true;

   constant clkper      : time      := 10 ns;

   signal clk           : std_logic;
   signal reset         : std_logic;

   -- input interface
   signal sof_n         : std_logic;
   signal sop_n         : std_logic;
   signal eop_n         : std_logic;
   signal eof_n         : std_logic;
   signal src_rdy_n     : std_logic;
   signal dst_rdy_n     : std_logic;

   -- output interface
   signal sof           : std_logic;
   signal sohdr         : std_logic;
   signal eohdr         : std_logic;
   signal hdr_frame     : std_logic;
   signal sopld         : std_logic;
   signal eopld         : std_logic;
   signal pld_frame     : std_logic;
   signal softr         : std_logic;
   signal eoftr         : std_logic;
   signal ftr_frame     : std_logic;
   signal eof           : std_logic;
   signal src_rdy       : std_logic;
   signal dst_rdy       : std_logic;


-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

   uut : entity work.FL_DEC
      generic map(
         HEADER      => TEST_HEADER,
         FOOTER      => TEST_FOOTER
      )
      port map(
         CLK         => clk,
         RESET       => reset,
         -- input signals: FrameLink interface
         SOF_N       => sof_n,
         SOP_N       => sop_n,
         EOP_N       => eop_n,
         EOF_N       => eof_n,
         SRC_RDY_N   => src_rdy_n,
         DST_RDY_N   => dst_rdy_n,
         -- output signa-- outputls
         SOF         => sof,
         SOHDR       => sohdr,
         EOHDR       => eohdr,
         HDR_FRAME   => hdr_frame,
         SOPLD       => sopld,
         EOPLD       => eopld,
         PLD_FRAME   => pld_frame,
         SOFTR       => softr,
         EOFTR       => eoftr,
         FTR_FRAME   => ftr_frame,
         EOF         => eof,
         SRC_RDY     => src_rdy,
         DST_RDY     => dst_rdy
      );

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

-- ----------------------------------------------------------------------------
--                         Main testbench process
-- ----------------------------------------------------------------------------
tb : process

begin
   reset       <= '1';
   sof_n       <= '1';
   sop_n       <= '1';
   eop_n       <= '1';
   eof_n       <= '1';
   src_rdy_n   <= '0';
   dst_rdy     <= '1';

   wait for 10*clkper;
   reset <= '0';

   wait for 5*clkper;

   -- -------------------------------------------------------------------------
   -- first frame
   sof_n       <= '0';
   sop_n       <= '0';
   wait for clkper;
   sof_n       <= '1';
   sop_n       <= '1';
   wait for 5*clkper;   -- header
   eop_n       <= '0';
   wait for clkper;
   eop_n       <= '1';

   sop_n       <= '0';
   wait for clkper;
   sof_n       <= '1';
   sop_n       <= '1';
   wait for 5*clkper;   -- packet
   eop_n       <= '0';
   wait for clkper;
   eop_n       <= '1';

   sop_n       <= '0';
   wait for clkper;
   sof_n       <= '1';
   sop_n       <= '1';
   wait for 5*clkper;   -- footer
   eop_n       <= '0';
   eof_n       <= '0';
   wait for clkper;
   eof_n       <= '1';
   eop_n       <= '1';


   wait for 10*clkper;   -- footer

   -- -------------------------------------------------------------------------
   -- second frame
   -- try one word sections -> EOP and SOP in one clock cycle

   sof_n       <= '0';
   sop_n       <= '0';
   eop_n       <= '0';
   wait for clkper;
   sof_n       <= '1';
   sop_n       <= '0';
   eop_n       <= '1';

   wait for clkper;
   sop_n       <= '1';
   wait for 5*clkper;   -- packet
   eop_n       <= '0';
   wait for clkper;
   eop_n       <= '1';

   sop_n       <= '0';
   eop_n       <= '0';
   eof_n       <= '0';
   wait for clkper;
   eof_n       <= '1';
   eop_n       <= '1';
   sop_n       <= '1';

   wait;
end process;

end architecture behavioral;
