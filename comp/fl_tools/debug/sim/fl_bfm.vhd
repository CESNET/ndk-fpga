--
-- fl_bfm.vhd: Simulation component for Frame link
-- Copyright (C) 2006 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
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
use std.textio.all;
use work.fl_pkg.all;
use work.fl_bfm_rdy_pkg.all;
use work.FL_BFM_pkg.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FL_BFM is
   generic(
      -- FrameLink data bus width
      -- only 8, 16, 32, 64 and 128 bit fl bus supported
      DATA_WIDTH  : integer;
      -- uniqe identity of FL_BFM as one of 16 posible FL_BFMs in design
      FL_BFM_ID   : integer
   );
   port(
      -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame link output Interface

      TX_DATA        : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_REM         : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
     );
end entity FL_BFM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FL_BFM_ARCH of FL_BFM is
  SHARED VARIABLE Cmd : CmdTypeItem;
  signal test: CmdTypeItem;
  signal SRC_RDY_N : std_logic;
  signal SRC_DRIVE : std_logic;

  signal flCmd : flCmdTypeItem := ('0','Z','Z');

  PROCEDURE Write(variable trans      :  IN CmdTypeItem;
                  signal   CLK        :  IN std_logic;
                  signal   DATA       : OUT std_logic_vector(DATA_WIDTH-1 downto 0);
                  signal   DREM       : OUT std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
                  signal   SOF_N      : OUT std_logic;
                  signal   SOP_N      : OUT std_logic;
                  signal   EOP_N      : OUT std_logic;
                  signal   EOF_N      : OUT std_logic;
                  signal   SRC_RDY_N  :  IN std_logic;
                  signal   DST_RDY_N  :  IN std_logic;
		  signal   Enable     : OUT std_logic) IS
  variable index     : integer;
  variable byteCount : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
  variable i         : integer;
  variable maxRem    : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

  BEGIN
    Enable <= '0';
    maxRem := (others => '1');
    index := 0;

    wait until (CLK'event and CLK='1' and SRC_RDY_N = '0'); --and DST_RDY_N='0');
    Enable <= '1';
      while (index <= trans.Length) loop
        DATA(7 downto 0) <= trans.Data(index).Data;
        byteCount := (others => '0');
	i:= 1;
        if (trans.Data(index).StartControl = SOF) then
          SOF_N <= '0';
          SOP_N <= '0';
        elsif (trans.Data(index).StartControl = SOP) then
          SOF_N <= '1';
          SOP_N <= '0';
        elsif (trans.Data(index).StartControl = NOP) then
          SOF_N <= '1';
          SOP_N <= '1';
        end if;
	if (DATA_WIDTH > 8) then
	   if (trans.Data(index).EndControl = NOP) then
              while ((index + 1 <= trans.Length) and byteCount < maxRem) loop
                 index := index + 1;
                 byteCount := byteCount + '1';
	         i := i + 1;
                 DATA((i * 8) - 1 downto (i - 1) * 8) <= trans.Data(index).Data;
	         if ((trans.Data(index).EndControl = EOF) or (trans.Data(index).EndControl = EOP)) then
	            exit;
	         end if;
              end loop;
	    end if;
	end if;
        if (trans.Data(index).EndControl = EOF) then
          EOF_N <= '0';
          EOP_N <= '0';
        elsif (trans.Data(index).EndControl = EOP) then
          EOF_N <= '1';
          EOP_N <= '0';
        elsif(trans.Data(index).EndControl = NOP) then
         EOF_N <= '1';
         EOP_N <= '1';
        end if;
	DREM <= byteCount;
        wait until (CLK'event and CLK='1' and SRC_RDY_N = '0' and DST_RDY_N='0');
	index := index + 1;
      end loop;
  Enable <= '0';
  END Write;

 begin

 gen0: if (FL_BFM_ID = 0) generate
   flCmd_0.Ack <= flCmd.Ack;
   flCmd_0.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_0.Req;
 end generate gen0;

 gen1: if (FL_BFM_ID = 1) generate
   flCmd_1.Ack <= flCmd.Ack;
   flCmd_1.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_1.Req;
 end generate gen1;

 gen2: if (FL_BFM_ID = 2) generate
   flCmd_2.Ack <= flCmd.Ack;
   flCmd_2.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_2.Req;
 end generate gen2;

 gen3: if (FL_BFM_ID = 3) generate
   flCmd_3.Ack <= flCmd.Ack;
   flCmd_3.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_3.Req;
 end generate gen3;

 gen4: if (FL_BFM_ID = 4) generate
   flCmd_4.Ack <= flCmd.Ack;
   flCmd_4.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_4.Req;
 end generate gen4;

 gen5: if (FL_BFM_ID = 5) generate
   flCmd_5.Ack <= flCmd.Ack;
   flCmd_5.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_5.Req;
 end generate gen5;

 gen6: if (FL_BFM_ID = 6) generate
   flCmd_6.Ack <= flCmd.Ack;
   flCmd_6.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_6.Req;
 end generate gen6;

 gen7: if (FL_BFM_ID = 7) generate
   flCmd_7.Ack <= flCmd.Ack;
   flCmd_7.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_7.Req;
 end generate gen7;

 gen8: if (FL_BFM_ID = 8) generate
   flCmd_8.Ack <= flCmd.Ack;
   flCmd_8.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_8.Req;
 end generate gen8;

 gen9: if (FL_BFM_ID = 9) generate
   flCmd_9.Ack <= flCmd.Ack;
   flCmd_9.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_9.Req;
 end generate gen9;

 genA: if (FL_BFM_ID = 10) generate
   flCmd_A.Ack <= flCmd.Ack;
   flCmd_A.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_A.Req;
 end generate genA;

 genB: if (FL_BFM_ID = 11) generate
   flCmd_B.Ack <= flCmd.Ack;
   flCmd_B.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_B.Req;
 end generate genB;

 genC: if (FL_BFM_ID = 12) generate
   flCmd_C.Ack <= flCmd.Ack;
   flCmd_C.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_C.Req;
 end generate genC;

 genD: if (FL_BFM_ID = 13) generate
   flCmd_D.Ack <= flCmd.Ack;
   flCmd_D.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_D.Req;
 end generate genD;

 genE: if (FL_BFM_ID = 14) generate
   flCmd_E.Ack <= flCmd.Ack;
   flCmd_E.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_E.Req;
 end generate genE;

 genF: if (FL_BFM_ID = 15) generate
   flCmd_F.Ack <= flCmd.Ack;
   flCmd_F.ReqAck <= flCmd.ReqAck;
   flCmd.Req <= flCmd_F.Req;
 end generate genF;

  SEND:process
  begin
    TX_DATA      <= (others => '0');
    TX_REM       <= (others => '0');
    TX_SOF_N     <= '1';
    TX_EOF_N     <= '1';
    TX_SOP_N     <= '1';
    TX_EOP_N     <= '1';

    LOOP
      flCmd.Ack    <= '0';
      flCmd.ReqAck <= '0';

      SRC_DRIVE    <= '0';

      -- Get Command
      WHILE (flCmd.Req = '0') LOOP
         WAIT UNTIL (flCmd.Req = '1');
      END LOOP;

      -- Send Request Acknowledge
      flCmd.ReqAck <= NOT(flCmd.ReqAck);
      -- Wait for Reqest Deasert
      WAIT ON flCmd.Req;


      ReadCommand(Cmd, FL_BFM_ID);
      test<=Cmd;
      --SRC_DRIVE <= '1';
      Write(Cmd, CLK, TX_DATA, TX_REM, TX_SOF_N, TX_SOP_N, TX_EOP_N, TX_EOF_N, SRC_RDY_N, TX_DST_RDY_N, SRC_DRIVE);
      SRC_DRIVE <= '0';

      -- Send Command done
      flCmd.Ack <= '1';
      wait until (CLK'event and CLK='1');
    end loop;
  end process;

  -- Drive SRC_RDY_N ---------------------------------------------------------------
  DRIVE_SRC_RDY_N: PROCESS
  BEGIN
    LOOP
      IF (Cmd.RDYDriver = EVER) then
         DriveRdyNAll(CLK, SRC_RDY_N);
      elsif (Cmd.RDYDriver = ONOFF) then
         DriveRdyN50_50(CLK, SRC_RDY_N);
      elsif (Cmd.RDYDriver = RND) then
         DriveRdyNRnd(CLK, SRC_RDY_N);
      end if;
    END LOOP;
  END PROCESS;

 TX_SRC_RDY_N <= SRC_RDY_N or not SRC_DRIVE;

end architecture FL_BFM_ARCH;
