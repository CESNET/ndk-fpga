-- flu_bfm.vhd: Simulation component for Frame Link Unaligned
-- Copyright (C) 2014 CESNET
-- Author(s): Ivan Bryndza <xbrynd00@stud.feec.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.flu_bfm_rdy_pkg.all;
use work.flu_bfm_pkg.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity FLU_BFM is
   generic(
      -- FrameLinkUnaligned data bus width
      -- only 8, 16, 32, 64, 128, 256, 512 bit flu bus supported
      DATA_WIDTH    : integer;
      SOP_POS_WIDTH : integer;
      -- uniqe identity of FLU_BFM as one of 16 posible FLU_BFMs in design
      FLU_BFM_ID    : integer
   );
   port(
      -- Common interface
      RESET          : in  std_logic;
      CLK            : in  std_logic;

      -- Frame link output Interface

      TX_DATA      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      TX_SOP_POS   : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      TX_EOP_POS   : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      TX_SOP       : out std_logic;
      TX_EOP       : out std_logic;
      TX_SRC_RDY   : out std_logic;
      TX_DST_RDY   : in  std_logic
     );
end entity FLU_BFM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FLU_BFM_ARCH of FLU_BFM is
   SHARED VARIABLE Cmd : CmdTypeItem;
   signal test: CmdTypeItem;
   signal SRC_RDY   : std_logic;
   signal SRC_DRIVE : std_logic;

   signal fluCmd : fluCmdTypeItem := ('0','Z','Z');

   -- function adjust space between packets according to SOP_POS_WIDTH and it's step
   function check_space (space: integer; index: integer; step: integer) return integer is
   variable var_space : integer;
   begin
      if (space /= 0) then
         var_space := index + space;
         if (not((var_space mod step) = 0)) then
            var_space := space - (var_space mod step) + step;
         else
            var_space := space;
         end if;
      else
         var_space := index;
         if not((var_space mod step) = 0) then
            var_space := var_space - (var_space mod step) + step;
            var_space := var_space - index;
         else
            var_space := 0;
         end if;
      end if;
      return var_space;
   end check_space;

   PROCEDURE Write(variable trans      :  INOUT CmdTypeItem;
                   signal   CLK        :  IN std_logic;
                   signal   DATA       : OUT std_logic_vector(DATA_WIDTH-1 downto 0);
                   signal   TX_SOP_POS    : OUT std_logic_vector(SOP_POS_WIDTH-1 downto 0);
                   signal   TX_EOP_POS    : OUT std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
                   signal   TX_SOP        : OUT std_logic;
                   signal   TX_EOP        : OUT std_logic;
                   signal   SRC_RDY    :  IN std_logic;
                   signal   DST_RDY    :  IN std_logic;
		             signal   Enable     : OUT std_logic) IS
   variable index        : integer; -- index for SOP,EOP
   variable data_index   : integer; -- index for Data
   variable last_index   : integer; -- stored value of index after every (CLK'event and CLK = 1 and SRC_RDY = 1 and DST_RDY = 1)
   variable bytes        : integer; -- number of written bytes in the output (include zeros) from begining to the end of file
   variable count        : integer; -- number of zeros between 2 packets
   variable count_sop    : integer; -- added value to count if 2x SOP in one transaction detected
   variable count_eop    : integer; -- added value to count 2 packets if 2x EOP in one transaction detected
   variable last_count   : integer; -- value of zeros left from last transaction (used when sop_set > 1 or eop_set > 1)
   variable set          : integer; -- (set = 1 when count /= 0) and (set = 0 when count = 0) - used for TX_SOP set
   variable sop_set      : integer; -- number of SOP in one transaction (when sop_set > 1 - space must be adjusted)
   variable eop_set      : integer; -- number of EOP in one transaction (when Eop_set > 1 - space must be adjusted)
   variable sop_pos      : integer; -- position of SOP
   variable eop_pos      : integer; -- position of EOP
   variable byteCount    : integer; -- number of written bytes in the output (max malue = maxBytes)
   variable maxBytes     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   variable maxBytes_int : integer;
   variable i            : integer;
   variable diff_space   : integer; -- difference between space read from file(trans.Data(index).Space) and adjusted space(count)
   variable sop_pos_step : integer := ((DATA_WIDTH/8)/(2**SOP_POS_WIDTH));
   variable zeros        : std_logic_vector(7 downto 0);
   variable get_ready    : integer;

   BEGIN
      Enable       <='0';
      index        := 0;
      data_index   := 0;
      last_index   := 0;
      bytes        := 0;
      count        := 0;
      count_sop    := 0;
      count_eop    := 0;
      last_count   := 0;
      set          := 0;
      maxBytes     := (others => '1');
      maxBytes_int := conv_integer(maxBytes) + 1;
      zeros        := (others => '0');
      get_ready    := 0;

      loop
         wait until (CLK'event and CLK='1');
         wait for 0.5 ps;
         if(SRC_RDY = '1' and DST_RDY = '1') then
            exit;
         end if;
      end loop;
      Enable <= '1';
      while (index <= trans.Length) loop
         sop_set   := 0;
         eop_set   := 0;
         sop_pos   := -1;
         eop_pos   := -1;
         bytecount := 0;
	      i         := 0;

         -- set value of count if conditions are met
         if (set = 0 and trans.Data(index).StartControl = SOP) then
            -- count_eop, count_sop are space adjustments if 2x SOP or 2x EOP found in one transaction
            count := check_space(trans.Data(index).Space + count_eop + count_sop, bytes, sop_pos_step);
            set := 1;
         end if;

         -- fill output Data (DATA_WIDTH-1 downto 0);
         while ((index  <= trans.Length) and byteCount < maxBytes_int) loop
            sop_pos := sop_pos + 1;
            eop_pos := eop_pos + 1;
            byteCount := byteCount + 1;
	         i := i + 1;

            -- if some space between packets fill it with zeros
            if (count > 0) then
               DATA((i * 8) - 1 downto (i - 1) * 8) <= zeros;
               count := count - 1;
            -- else fill Data with data from file
            else
               DATA((i * 8) - 1 downto (i - 1) * 8) <= trans.Data(data_index).Data;
               data_index := data_index + 1;
               set := 0;
            end if;

            -- if SOP detected ("$" in input file)
            if (trans.Data(index).StartControl = SOP and set = 0) then
               TX_SOP <= '1';
               TX_SOP_POS <= conv_std_logic_vector(sop_pos/sop_pos_step , SOP_POS_WIDTH);
               sop_set := sop_set + 1;
            elsif (sop_set = 0) then
               TX_SOP <= '0';
               TX_SOP_POS <= (others => '0');
            end if;

            -- if EOP detected ("$" in input file)
	         if (trans.Data(index).EndControl = EOP and set = 0) then
               -- set TX_EOP and TX_EOP_POS
               TX_EOP <= '1';
               TX_EOP_POS <= conv_std_logic_vector(eop_pos, log2(DATA_WIDTH/8));
               -- set and adjust space
               count := check_space(trans.Data(index + 1).Space + count_eop + count_sop, bytes + 1, sop_pos_step);
               -- set := 1 only when one EOP is in one transaction
               if (eop_set = 0) then
                  set := 1;
                  diff_space := count - trans.Data(index + 1).Space;
               end if;
               eop_set := eop_set + 1;
            elsif(trans.Data(index).EndControl = NOP and eop_set = 0) then
               TX_EOP <= '0';
	         end if;

            --sychronize index with data_index
            index := data_index;
            bytes := bytes + 1;
         end loop;

         count_sop := 0;
         count_eop := 0;
         -- if 2x SOP detected in this transaction don't wait for CLK and SRC_RDY and DST_RDY (index := last_index)
         -- and refill data (data_index := last_index)(bytes := bytes - DATA_WIDTH/8)
         -- with corrected value of space (count_sop := ...)
         -- and dont't forget to fill space in front of first packet in this transaction (count := last_count)
         if (sop_set > 1) then
            index := last_index;
            data_index := last_index;
            bytes := bytes - DATA_WIDTH/8;
            count_sop := DATA_WIDTH/8 - sop_pos + diff_space;
            count := last_count;
            set := 1;
         -- if 2x EOP detected in this transaction - similar process
         elsif (eop_set > 1) then
            index := last_index;
            data_index := last_index;
            bytes := bytes - DATA_WIDTH/8;
            count_eop := DATA_WIDTH/8 - eop_pos + diff_space;
            count := last_count;
            set := 1;
         end if;


         -- if all zeros or if 2x SOP or 2x EOP detected ignore clock and source ready and destination ready and refill Data
         if not(last_index = index and index < trans.Length) then
            loop
               wait until (CLK'event and CLK='1');
               wait for 0.5 ps;
               if(SRC_RDY = '1' and DST_RDY = '1') then
                  exit;
               end if;
            end loop;
         end if;
         -- store values after transaction
         last_index := index;
         last_count := count;
      end loop;
      Enable <= '0';
   END Write;

begin

   gen0: if (FLU_BFM_ID = 0) generate
      fluCmd_0.Ack <= fluCmd.Ack;
      fluCmd_0.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_0.Req;
   end generate gen0;

   gen1: if (FLU_BFM_ID = 1) generate
      fluCmd_1.Ack <= fluCmd.Ack;
      fluCmd_1.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_1.Req;
   end generate gen1;

   gen2: if (FLU_BFM_ID = 2) generate
      fluCmd_2.Ack <= fluCmd.Ack;
      fluCmd_2.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_2.Req;
   end generate gen2;

   gen3: if (FLU_BFM_ID = 3) generate
      fluCmd_3.Ack <= fluCmd.Ack;
      fluCmd_3.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_3.Req;
   end generate gen3;

   gen4: if (FLU_BFM_ID = 4) generate
      fluCmd_4.Ack <= fluCmd.Ack;
      fluCmd_4.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_4.Req;
   end generate gen4;

   gen5: if (FLU_BFM_ID = 5) generate
      fluCmd_5.Ack <= fluCmd.Ack;
      fluCmd_5.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_5.Req;
   end generate gen5;

   gen6: if (FLU_BFM_ID = 6) generate
      fluCmd_6.Ack <= fluCmd.Ack;
      fluCmd_6.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_6.Req;
   end generate gen6;

   gen7: if (FLU_BFM_ID = 7) generate
      fluCmd_7.Ack <= fluCmd.Ack;
      fluCmd_7.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_7.Req;
   end generate gen7;

   gen8: if (FLU_BFM_ID = 8) generate
      fluCmd_8.Ack <= fluCmd.Ack;
      fluCmd_8.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_8.Req;
   end generate gen8;

   gen9: if (FLU_BFM_ID = 9) generate
      fluCmd_9.Ack <= fluCmd.Ack;
      fluCmd_9.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_9.Req;
   end generate gen9;

   genA: if (FLU_BFM_ID = 10) generate
      fluCmd_A.Ack <= fluCmd.Ack;
      fluCmd_A.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_A.Req;
   end generate genA;

   genB: if (FLU_BFM_ID = 11) generate
      fluCmd_B.Ack <= fluCmd.Ack;
      fluCmd_B.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_B.Req;
   end generate genB;

   genC: if (FLU_BFM_ID = 12) generate
      fluCmd_C.Ack <= fluCmd.Ack;
      fluCmd_C.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_C.Req;
   end generate genC;

   genD: if (FLU_BFM_ID = 13) generate
      fluCmd_D.Ack <= fluCmd.Ack;
      fluCmd_D.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_D.Req;
   end generate genD;

   genE: if (FLU_BFM_ID = 14) generate
      fluCmd_E.Ack <= fluCmd.Ack;
      fluCmd_E.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_E.Req;
   end generate genE;

   genF: if (FLU_BFM_ID = 15) generate
      fluCmd_F.Ack <= fluCmd.Ack;
      fluCmd_F.ReqAck <= fluCmd.ReqAck;
      fluCmd.Req <= fluCmd_F.Req;
   end generate genF;

   SEND:process
   begin
      TX_DATA      <= (others => '0');
      TX_EOP_POS   <= (others => '0');
      TX_SOP_POS   <= (others => '0');
      TX_EOP       <= '0';
      TX_SOP       <= '0';

      LOOP
         fluCmd.Ack    <= '0';
         fluCmd.ReqAck <= '0';

         SRC_DRIVE    <= '0';

         -- Get Command
         WHILE (fluCmd.Req = '0') LOOP
            WAIT UNTIL (fluCmd.Req = '1');
         END LOOP;

         -- Send Request Acknowledge
         fluCmd.ReqAck <= NOT(fluCmd.ReqAck);
         -- Wait for Reqest Deasert
         WAIT ON fluCmd.Req;


         ReadCommand(Cmd, FLU_BFM_ID);
         test<=Cmd;
         --SRC_DRIVE <= '1';
         Write(Cmd, CLK, TX_DATA, TX_SOP_POS, TX_EOP_POS, TX_SOP, TX_EOP, SRC_RDY, TX_DST_RDY, SRC_DRIVE);
         --SRC_DRIVE <= '0';

         -- Send Command done
         fluCmd.Ack <= '1';
         wait until (CLK'event and CLK='1');
      end loop;
   end process;

  -- Drive SRC_RDY_N ---------------------------------------------------------------
   DRIVE_SRC_RDY: PROCESS
   BEGIN
      LOOP
         IF (Cmd.RDYDriver = EVER) then
            DriveRdyNAll(CLK, SRC_RDY);
         elsif (Cmd.RDYDriver = ONOFF) then
            DriveRdyN50_50(CLK, SRC_RDY);
         elsif (Cmd.RDYDriver = RND) then
            DriveRdyNRnd(CLK, SRC_RDY);
         end if;
      END LOOP;
   END PROCESS;

   TX_SRC_RDY <= SRC_RDY and SRC_DRIVE;
--process(SRC_DRIVE)
--begin
--   if SRC_DRIVE = '1' then
--      TX_SRC_RDY <= SRC_DRIVE;
--   else
--      TX_SRC_RDY <= '0';
--   end if;
--end process;
end architecture FLU_BFM_ARCH;
