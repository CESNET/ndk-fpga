--
-- ib_sim.vhd: Simulation component for internal bus
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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

library STD_DEVELOPERSKIT;
use     STD_DEVELOPERSKIT.std_iopak.all;       -- To_string

use work.math_pack.all;
use work.ib_pkg.all;
use work.ib_bfm_pkg.all;
use work.ib_bfm_rdy_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
ENTITY IB_BFM IS
   GENERIC (
       MEMORY_BASE_ADDR : std_logic_vector(63 downto 0) := X"FFFFFFFF00000000"; -- Memory Base ADDR
       MEMORY_SIZE      : integer := 1024; -- Defaul 1024 Bytes
       MEMORY_DELAY     : integer := 10    -- Delay before sending completition
       );
   PORT (
      CLK          : in  std_logic;
      -- Internal Bus Interface
      IB           : inout t_internal_bus64
      );
END ENTITY IB_BFM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
ARCHITECTURE IB_BFM_ARCH OF IB_BFM IS

   -- Request for completition
   SIGNAL ComplReq               : IbCmdType := ('0', 'Z', 'Z');
   SHARED VARIABLE ComplDataCmdV : IbCmdVType;

   -- Transactions
   SHARED VARIABLE LclIbCmdV        : IbCmdVType;
   SHARED VARIABLE LclIbCmdVReceive : IbCmdVType;

   -- Host Memory
   TYPE MemoryType IS ARRAY (0 TO MEMORY_SIZE/8) of std_logic_vector(63 downto 0);
   SHARED VARIABLE Memory : MemoryType;

   -- Logging settings
   SHARED VARIABLE LogTranscript : boolean := true;
   SHARED VARIABLE LogFile       : boolean := false;

   -- Write Align Type
   TYPE WriteAlignType IS
    RECORD
      Align    : integer;
      AlignReg : std_logic_vector(63 downto 0);
    END RECORD;

   ----------------------------------------------------------------------------
   -- Completition FIFO for G2LR
   CONSTANT FIFO_LEN : integer := 256;
   TYPE FifoType IS ARRAY (0 TO FIFO_LEN-1) of IbCmdVType;
   TYPE CompletitionFifoType IS
    RECORD
      BeginPtr : integer;
      EndPtr   : integer;
      Items    : integer;
      Empty    : boolean;
      Fifo     : FifoType;
    END RECORD;
   SHARED VARIABLE ComplFifo : CompletitionFifoType;

   -- -------------------------------------------------------------------------
   PROCEDURE InitFifo IS
   BEGIN
     ComplFifo.EndPtr   := 0;
     ComplFifo.BeginPtr := 0;
     ComplFifo.Empty    := true;
     ComplFifo.Items    := 0;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   PROCEDURE insertFifo(input  :  IN  IbCmdVType) IS
   BEGIN
     ComplFifo.Fifo(ComplFifo.EndPtr) := input;
     ComplFifo.EndPtr := ComplFifo.EndPtr+1;
     ComplFifo.Items  := ComplFifo.Items+1;
     if (ComplFifo.EndPtr = FIFO_LEN) then
       ComplFifo.EndPtr := 0;
     end if;
     ComplFifo.Empty  := false;
     ASSERT (ComplFifo.EndPtr /= ComplFifo.BeginPtr or ComplFifo.Items=0)
            REPORT "IB_BFM: Completition fifo overflow";
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   PROCEDURE getFifo(output : INOUT IbCmdVType) IS
   BEGIN
     if (not ComplFifo.Empty) then
       output:=ComplFifo.Fifo(ComplFifo.BeginPtr);
       ComplFifo.BeginPtr := ComplFifo.BeginPtr + 1;
       if (ComplFifo.BeginPtr = FIFO_LEN) then
         ComplFifo.BeginPtr := 0;
       end if;
       ComplFifo.Items:=ComplFifo.Items-1;
       ComplFifo.Empty:=ComplFifo.BeginPtr=ComplFifo.EndPtr;
     end if;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   PROCEDURE to_bit_vector(input  :  IN  std_logic_vector;
                           output :  OUT bit_vector) IS
     VARIABLE i : integer;
   BEGIN
   for i in 0 to input'high loop
      if (input(i) = '1') then
        output(i) := '1';
      else
        output(i) := '0';
      end if;
   end loop;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- ShowCommand Info
   PROCEDURE ShowCommandInfo(cmdV :  IN IbCmdVType; info : in string) IS
      VARIABLE SrcAddr    : bit_vector(31 downto 0);
      VARIABLE DstAddr    : bit_vector(31 downto 0);
      VARIABLE LocalAddr  : bit_vector(31 downto 0);
      VARIABLE GlobalAddr : bit_vector(63 downto 0);
      VARIABLE Data       : bit_vector(63 downto 0);
      VARIABLE i          : integer;
      file output         : ascii_text open write_mode  is "STD_OUTPUT";
      file outfile        : ascii_text open append_mode is "internal_bus.log";
   BEGIN
    to_bit_vector(cmdV.Di.SrcAddr,    SrcAddr);
    to_bit_vector(cmdV.Di.DstAddr,    DstAddr);
    to_bit_vector(cmdV.Di.LocalAddr,  LocalAddr);
    to_bit_vector(cmdV.Di.GlobalAddr, GlobalAddr);



    CASE cmdV.CmdOp IS

       WHEN LocalRead =>
         if (LogTranscript) then
           fprint(output,"IB_BFM: %s Local2Local Read:  SrcAddr: 0x%s DstAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(SrcAddr, "%x"), to_string(DstAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         if (LogFile) then
           fprint(outfile,"IB_BFM: %s Local2Local Read:  SrcAddr: 0x%s DstAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(SrcAddr, "%x"), to_string(DstAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;

       WHEN LocalWrite =>
         if (LogTranscript) then
           fprint(output,"IB_BFM: %s Local2Local Write: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(DstAddr, "%x"), to_string(SrcAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         if (LogFile) then
           fprint(outfile,"IB_BFM: %s Local2Local Write: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(DstAddr, "%x"), to_string(SrcAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         i:= 0;
         while i < cmdV.Di.Length loop
           to_bit_vector(cmdV.Di.Data(i/8), Data);
           if (LogTranscript) then
             fprint(output,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;
           if (LogFile) then
             fprint(outfile,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;

           i:=i+8;
         end loop;

       WHEN Completition =>
         if (LogTranscript) then
           fprint(output,"IB_BFM: %s Completition: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s LastFlag: %s\n",
                          info, to_string(DstAddr, "%x"), to_string(SrcAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length), to_string(cmdV.Di.LastFlag));
         end if;
         if (LogFile) then
           fprint(outfile,"IB_BFM: %s Completition: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s LastFlag: %s\n",
                          info, to_string(DstAddr, "%x"), to_string(SrcAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length), to_string(cmdV.Di.LastFlag));
         end if;
         i:= 0;
         while i < cmdV.Di.Length loop
           to_bit_vector(cmdV.Di.Data(i/8), Data);
           if (LogTranscript) then
             fprint(output,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;
           if (LogFile) then
             fprint(outfile,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;
           i:=i+8;
         end loop;

       WHEN G2LR =>
         if (LogTranscript) then
           fprint(output,"IB_BFM: %s Global2Local Read:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(GlobalAddr, "%x"), to_string(LocalAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         if (LogFile) then
           fprint(outfile,"IB_BFM: %s Global2Local Read:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(GlobalAddr, "%x"), to_string(LocalAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;

       WHEN L2GW =>
         if (LogTranscript) then
           fprint(output,"IB_BFM: %s Local2Global Write:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(GlobalAddr, "%x"), to_string(LocalAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         if (LogFile) then
           fprint(outfile,"IB_BFM: %s Local2Global Write:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                          info, to_string(GlobalAddr, "%x"), to_string(LocalAddr, "%x"),to_string(cmdV.Di.Tag),
                          to_string(cmdV.Di.Length));
         end if;
         i:= 0;
         while i < cmdV.Di.Length loop
           to_bit_vector(cmdV.Di.Data(i/8), Data);
           if (LogTranscript) then
             fprint(output,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;
           if (LogFile) then
             fprint(outfile,"        DATA: 0x%s\n", to_string(Data, "%x"));
           end if;
           i:=i+8;
         end loop;

       WHEN others =>

    END CASE;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Init Align
   PROCEDURE AlignInit(Align :  IN integer; WriteAlign : INOUT WriteAlignType) IS
   BEGIN
     WriteAlign.Align    := Align;
     WriteAlign.AlignReg := X"0000000000000000";
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- GetWriteCount
   FUNCTION GetWriteCount(Align  :  IN integer;
                          Length :  IN integer) RETURN integer IS
     VARIABLE Plus : integer;
   BEGIN
     if (((Length+Align) mod 8) > 0) then
       Plus := 1;
     else
       Plus := 0;
     end if;
     RETURN (Length+Align)/8 + Plus;
   END FUNCTION;

   -- -------------------------------------------------------------------------
   -- GetWriteData
   PROCEDURE GetWriteData(DataIn         : IN std_logic_vector(63 downto 0);
                          SIGNAL DataOut : OUT std_logic_vector(63 downto 0);
                          WriteAlign     : INOUT WriteAlignType) IS
   VARIABLE i : integer;
   VARIABLE j : integer;
   BEGIN
     if (WriteAlign.Align = 0) then
       DataOut <= DataIn;
     else
       j:=0;
       for i in WriteAlign.Align*8-1 downto 0 loop
         DataOut(i) <= WriteAlign.AlignReg(64-(WriteAlign.Align*8)+i);
       end loop;
       for i in WriteAlign.Align*8 to 63  loop
         DataOut(i) <= DataIn(j);
         j:=j+1;
       end loop;
       WriteAlign.AlignReg := DataIn;
     end if;
   END PROCEDURE;


   -- -------------------------------------------------------------------------
   -- Generate LocalRead Transaction
   PROCEDURE LocalRead (variable trans     :  IN IbCmdVType;
                        signal   CLK       :  IN std_logic;
                        signal   DATA      : OUT std_logic_vector(63 downto 0);
                        signal   SOP_N     : OUT std_logic;
                        signal   EOP_N     : OUT std_logic;
                        signal   SRC_RDY_N : OUT std_logic;
                        signal   DST_RDY_N :  IN std_logic) IS
   BEGIN

     DATA      <= trans.Di.SrcAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                  '0' & C_IB_L2LR_TRANSACTION & conv_std_logic_vector(trans.Di.Length,12);
     SRC_RDY_N <= '0';
     SOP_N     <= '0';
     EOP_N     <= '1';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');
     DATA      <= X"00000000" & trans.Di.DstAddr;
     SRC_RDY_N <= '0';
     SOP_N     <= '1';
     EOP_N     <= '0';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');
     SOP_N     <= '1';
     EOP_N     <= '1';
     SRC_RDY_N <= '1';
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Generate LocalWrite Transaction
   PROCEDURE LocalWrite(variable trans     :  IN IbCmdVType;
                        signal   CLK       :  IN std_logic;
                        signal   DATA      : OUT std_logic_vector(63 downto 0);
                        signal   SOP_N     : OUT std_logic;
                        signal   EOP_N     : OUT std_logic;
                        signal   SRC_RDY_N : OUT std_logic;
                        signal   DST_RDY_N :  IN std_logic) IS
     VARIABLE i           : integer;
     VARIABLE len         : integer;
     VARIABLE aux_len     : integer;
     VARIABLE count       : integer;
     VARIABLE WriteAlign  :  WriteAlignType;
   BEGIN
     -- Set maximum length to 0 in header
     if (trans.Di.Length = 4096) then
        aux_len:= 0;
     else
        aux_len:=trans.Di.Length;
     end if;

     -- Send HDR0
     DATA      <= trans.Di.DstAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                  '0' & C_IB_L2LW_TRANSACTION & conv_std_logic_vector(aux_len,12);
     SRC_RDY_N <= '0';
     SOP_N     <= '0';
     EOP_N     <= '1';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');

     -- Send HDR1
     DATA      <= X"00000000" & trans.Di.SrcAddr;
     SRC_RDY_N <= '0';
     SOP_N     <= '1';
     EOP_N     <= '1';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');

     -- Send DATA
     AlignInit(conv_integer(trans.Di.DstAddr(2 downto 0)), WriteAlign);
     len   := trans.Di.Length;
     count := GetWriteCount(conv_integer(trans.Di.DstAddr(2 downto 0)),conv_integer(trans.Di.Length));
     for i in 0 to count-1 loop
       if (len > 0) then
         GetWriteData(trans.Di.Data(i), DATA, WriteAlign);
       else
         GetWriteData(X"0000000000000000", DATA, WriteAlign);
       end if;
       SRC_RDY_N <= '0';
       SOP_N     <= '1';
       if (i = (count-1)) then
         EOP_N   <= '0';
       else
         EOP_N   <= '1';
       end if;
       wait until (CLK'event and CLK='1' and DST_RDY_N='0');
       len := len - 8;
     end loop;

     SOP_N     <= '1';
     EOP_N     <= '1';
     SRC_RDY_N <= '1';
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Generate Completition Transaction
   PROCEDURE Completition(variable trans     :  IN IbCmdVType;
                          signal   CLK       :  IN std_logic;
                          signal   DATA      : OUT std_logic_vector(63 downto 0);
                          signal   SOP_N     : OUT std_logic;
                          signal   EOP_N     : OUT std_logic;
                          signal   SRC_RDY_N : OUT std_logic;
                          signal   DST_RDY_N :  IN std_logic) IS
     VARIABLE i          : integer;
     VARIABLE len        : integer;
     VARIABLE count      : integer;
     VARIABLE WriteAlign : WriteAlignType;
   BEGIN

     -- Send HDR0
     DATA      <= trans.Di.DstAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                  trans.Di.LastFlag & C_IB_RD_COMPL_TRANSACTION & conv_std_logic_vector(trans.Di.Length,12);
     SRC_RDY_N <= '0';
     SOP_N     <= '0';
     EOP_N     <= '1';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');

     -- Send HDR1
     DATA      <= X"00000000" & trans.Di.SrcAddr;
     SRC_RDY_N <= '0';
     SOP_N     <= '1';
     EOP_N     <= '1';
     wait until (CLK'event and CLK='1' and DST_RDY_N='0');

     -- Send DATA
     AlignInit(conv_integer(trans.Di.DstAddr(2 downto 0)),WriteAlign);
     len   := trans.Di.Length;
     count := GetWriteCount(conv_integer(trans.Di.DstAddr(2 downto 0)),conv_integer(trans.Di.Length));
     for i in 0 to count-1 loop
       if (len > 0) then
         GetWriteData(trans.Di.Data(i), DATA, WriteAlign);
       else
         GetWriteData(X"0000000000000000", DATA, WriteAlign);
       end if;
       SRC_RDY_N <= '0';
       SOP_N     <= '1';
       if (i = (count-1)) then
         EOP_N   <= '0';
       else
         EOP_N   <= '1';
       end if;
       wait until (CLK'event and CLK='1' and DST_RDY_N='0');
       len := len - 8;
     end loop;

     SOP_N     <= '1';
     EOP_N     <= '1';
     SRC_RDY_N <= '1';
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Receive Completition Transaction
   PROCEDURE ReceiveCompletition(signal CLK       :  IN std_logic;
                                 signal DATA      :  IN std_logic_vector(63 downto 0);
                                 signal SOP_N     :  IN std_logic;
                                 signal EOP_N     :  IN std_logic;
                                 signal SRC_RDY_N :  IN std_logic;
                                 signal DST_RDY_N :  IN std_logic) IS
     VARIABLE i     : integer;
   BEGIN
     -- Receive Header 1
     LclIbCmdVReceive.CmdOp       := Completition;
     LclIbCmdVReceive.Di.DstAddr  := DATA(63 downto 32);
     LclIbCmdVReceive.Di.Tag      := conv_integer(DATA(31 downto 16));
     LclIbCmdVReceive.Di.LastFlag := DATA(15);
     LclIbCmdVReceive.Di.Length   := conv_integer(DATA(11 downto  0));
     wait until (CLK'event and CLK='1' and SRC_RDY_N='0' and DST_RDY_N='0');
     -- Receive Header2
     LclIbCmdVReceive.Di.SrcAddr := DATA(63 downto 32);
     -- Receive Data
     i:=0;
     while i < LclIbCmdVReceive.Di.Length loop
       wait until (CLK'event and CLK='1' and SRC_RDY_N='0' and DST_RDY_N='0');
       LclIbCmdVReceive.Di.Data(i/8) := DATA;
       i:=i+8;
     end loop;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Receive G2LR Transaction
   PROCEDURE ReceiveG2LR(signal CLK       :  IN std_logic;
                         signal DATA      :  IN std_logic_vector(63 downto 0);
                         signal SOP_N     :  IN std_logic;
                         signal EOP_N     :  IN std_logic;
                         signal SRC_RDY_N :  IN std_logic;
                         signal DST_RDY_N :  IN std_logic) IS
   BEGIN
     -- Receive Header 1
     LclIbCmdVReceive.CmdOp                       := G2LR;
     LclIbCmdVReceive.Di.GlobalAddr(31 downto 0)  := DATA(63 downto 32);
     LclIbCmdVReceive.Di.Tag                      := conv_integer(DATA(31 downto 16));
     if (conv_integer(DATA(11 downto 0)) = 0) then
       LclIbCmdVReceive.Di.Length                 := 4096;
     else
       LclIbCmdVReceive.Di.Length                 := conv_integer(DATA(11 downto  0));
     end if;
     wait until (CLK'event and CLK='1' and SRC_RDY_N='0' and DST_RDY_N='0');
     -- Receive Header2
     LclIbCmdVReceive.Di.GlobalAddr(63 downto 32) := DATA(63 downto 32);
     LclIbCmdVReceive.Di.LocalAddr                := DATA(31 downto 0);
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Receive L2GW Transaction
   PROCEDURE ReceiveL2GW(signal CLK       :  IN std_logic;
                         signal DATA      :  IN std_logic_vector(63 downto 0);
                         signal SOP_N     :  IN std_logic;
                         signal EOP_N     :  IN std_logic;
                         signal SRC_RDY_N :  IN std_logic;
                         signal DST_RDY_N :  IN std_logic) IS
     VARIABLE i     : integer;
   BEGIN
     -- Receive Header 1
     LclIbCmdVReceive.CmdOp       := L2GW;
     LclIbCmdVReceive.Di.GlobalAddr(31 downto 0)  := DATA(63 downto 32);
     LclIbCmdVReceive.Di.Tag                      := conv_integer(DATA(31 downto 16));
     if (conv_integer(DATA(11 downto 0)) = 0) then
       LclIbCmdVReceive.Di.Length                 := 4096;
     else
       LclIbCmdVReceive.Di.Length                 := conv_integer(DATA(11 downto  0));
     end if;
     wait until (CLK'event and CLK='1' and SRC_RDY_N='0' and DST_RDY_N='0');
     -- Receive Header2
     LclIbCmdVReceive.Di.GlobalAddr(63 downto 32) := DATA(63 downto 32);
     LclIbCmdVReceive.Di.LocalAddr                := DATA(31 downto 0);
     -- Receive Data
     i:=0;
     while i < LclIbCmdVReceive.Di.Length loop
       wait until (CLK'event and CLK='1' and SRC_RDY_N='0' and DST_RDY_N='0');
       LclIbCmdVReceive.Di.Data(i/8) := DATA;
       i:=i+8;
     end loop;
   END PROCEDURE;


   -- -------------------------------------------------------------------------
   -- Load Host Memory Data
   PROCEDURE InitHostMemory IS
     VARIABLE i     : integer;
   BEGIN
     -- Init Memory with data
     i:=0;
     while i < LclIbCmdV.Di.Length loop
       Memory((LclIbCmdV.Di.MemAddr+i)/8) := LclIbCmdV.Di.Data(i/8);
       i:=i+8;
     end loop;

     while (LclIbCmdV.Di.MemAddr+i) < MEMORY_SIZE loop
       Memory((LclIbCmdV.Di.MemAddr+i)/8) := X"0000000000000000";
       i:=i+8;
     end loop;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Show Host Memory
   PROCEDURE ShowHostMemory IS
      VARIABLE Data       : bit_vector(63 downto 0);
      VARIABLE i          : integer;
      file output  : ascii_text open write_mode is "STD_OUTPUT";
      file outfile : ascii_text open append_mode is "internal_bus.log";
   BEGIN
     if (LogTranscript) then
       fprint(output,"IB_BFM: Host Memory Content\n");
       -- Show Content
       for i in 0 to MEMORY_SIZE/8 loop
         to_bit_vector(Memory(i), Data);
         fprint(output,"        DATA: 0x%s\n", to_string(Data, "%x"));
       end loop;
     end if;
     if (LogFile) then
       fprint(outfile,"IB_BFM: Host Memory Content\n");
     -- Show Content
       for i in 0 to MEMORY_SIZE/8 loop
         to_bit_vector(Memory(i), Data);
         fprint(outfile,"        DATA: 0x%s\n", to_string(Data, "%x"));
       end loop;
     end if;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Process L2GW Transaction (Save Transaction into memory)
   PROCEDURE ProcessL2GW(trans :  IN IbCmdVType) IS
     VARIABLE DstAddr : std_logic_vector(63 downto 0);
     VARIABLE start   : integer;
     VARIABLE i       : integer;
     VARIABLE j       : integer;
   BEGIN
   DstAddr := trans.Di.GlobalAddr - MEMORY_BASE_ADDR;
   ASSERT (DstAddr >=0 and DstAddr+trans.Di.Length <= MEMORY_SIZE)
     REPORT "L2GW outside of Host Memory address space";

   start := conv_integer(DstAddr(31 downto 0));
   j:=0;
   for i in start to (start+trans.Di.Length)-1 loop
     Memory(i/8)( (i mod 8)*8+7 downto (i mod 8)*8) :=
     trans.Di.Data(j/8)((j mod 8)*8+7 downto (j mod 8)*8);
     j:=j+1;
   end loop;
   END PROCEDURE;

   -- -------------------------------------------------------------------------
   -- Process G2LR Transaction (Save Transaction into Completition FIFO)
   PROCEDURE ProcessG2LR(trans :  IN IbCmdVType) IS
     VARIABLE DstAddr : std_logic_vector(63 downto 0);
     VARIABLE start   : integer;
     VARIABLE i       : integer;
     VARIABLE j       : integer;
     VARIABLE compl   : IbCmdVType;
   BEGIN
   DstAddr := trans.Di.GlobalAddr - MEMORY_BASE_ADDR;
   ASSERT (DstAddr >=0 and DstAddr+trans.Di.Length <= MEMORY_SIZE)
     REPORT "L2GW outside of Host Memory address space";

   compl.CmdOp       := Completition;
   compl.Di.DstAddr  := trans.Di.LocalAddr;
   compl.Di.SrcAddr  := X"FFFFFFFF";
   compl.Di.Tag      := trans.Di.Tag;
   compl.Di.Length   := trans.Di.Length;
   compl.Di.LastFlag := '1';

   -- Get Data from memory into field
   start := conv_integer(DstAddr(31 downto 0));
   j:=0;
   for i in start to (start+trans.Di.Length)-1 loop
     compl.Di.Data(j/8)((j mod 8)*8+7 downto (j mod 8)*8) :=
     Memory(i/8)( (i mod 8)*8+7 downto (i mod 8)*8);
     j:=j+1;
   end loop;
   -- Insert Completition Into Fifo
   insertFifo(compl);
   END PROCEDURE;

BEGIN


-- Send Packet Process --------------------------------------------------------
SEND_PACKETS: PROCESS
   file     log_file  : text;
BEGIN
  IB.DOWN.DATA      <= (others => '0');
  IB.DOWN.SOP_N     <= '1';
  IB.DOWN.EOP_N     <= '1';
  IB.DOWN.SRC_RDY_N <= '1';

  IbCmd.Ack         <= '0';
  ComplReq.Ack      <= '0';
  IbCmd.ReqAck      <= '0';
  ComplReq.ReqAck   <= '0';

  LOOP
    -- Get Command
    WHILE (IbCmd.Req = '0' and ComplReq.Req = '0') LOOP
       WAIT UNTIL (IbCmd.Req = '1' or ComplReq.Req = '1');
    END LOOP;

    if (IbCmd.Req = '1') then
      -- Send Request Acknowledge
      IbCmd.ReqAck <= NOT(IbCmd.ReqAck);
      -- Wait for Reqest Deasert
      WAIT ON IbCmd.Req;

      ReadIbCmdV(LclIbCmdV);
      ShowCommandInfo(LclIbCmdV,"Downstream");
      -- Process Command
      CASE LclIbCmdV.CmdOp IS
         WHEN LocalRead      =>
           LocalRead(LclIbCmdV, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
         WHEN LocalWrite     =>
           LocalWrite(LclIbCmdV, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
         WHEN Completition   =>
           Completition(LclIbCmdV, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
         WHEN InitMemory     =>
           InitHostMemory;
         WHEN InitMemoryFromAddr =>
           InitHostMemory;
         WHEN ShowMemory     =>
           ShowHostMemory;
         WHEN TranscriptLogging =>
            LogTranscript := LclIbCmdV.Di.Enable;
         WHEN FileLogging       =>
            LogFile       := LclIbCmdV.Di.Enable;
            if (LogFile) then
              file_open(log_file, "internal_bus.log", WRITE_MODE);
              file_close(log_file);
            end if;
         WHEN others            =>
      END CASE;

      -- Send Command done
      IbCmd.Ack <= NOT(IbCmd.Ack);
    end if;

    if (ComplReq.Req = '1') then
      -- Send Request Acknowledge
      ComplReq.ReqAck <= NOT(ComplReq.ReqAck);
      -- Wait for Reqest Deasert
      WAIT ON ComplReq.Req;

      ShowCommandInfo(ComplDataCmdV,"Downstream");
      Completition(ComplDataCmdV, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);

      -- Send Command done
      ComplReq.Ack <= NOT(ComplReq.Ack);
    end if;

  END LOOP;
END PROCESS;

-- Drive DST_RDY_N ---------------------------------------------------------------
DRIVE_DST_RDY_N: PROCESS
BEGIN
  LOOP
  DriveDstRdyN(CLK, IB.UP.DST_RDY_N);
  END LOOP;
END PROCESS;


-- Receive Packet Process --------------------------------------------------------
RECEIVE_PACKETS: PROCESS
BEGIN
  InitFifo; -- Init Completition fifo
--  IB.UP.DST_RDY_N <= '0'; Replaced by DRIVE_DST_RDY_N process
  LOOP
    wait until (CLK'event and CLK='1' and IB.UP.SRC_RDY_N='0' and IB.UP.SOP_N='0' and IB.UP.DST_RDY_N='0');

    CASE IB.UP.DATA(14 downto 12) IS
       WHEN C_IB_L2GW_TRANSACTION =>
         -- Receive Transaction
         ReceiveL2GW(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
         -- Show Transaction info
         ShowCommandInfo(LclIbCmdVReceive,"Upstream");
         -- Store transaction data into memory
         ProcessL2GW(LclIbCmdVReceive);
       WHEN C_IB_G2LR_TRANSACTION =>
         -- Receive Transaction
         ReceiveG2LR(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
         -- Show Transaction info
         ShowCommandInfo(LclIbCmdVReceive,"Upstream");
         -- Store Reqest into fifo
         ProcessG2LR(LclIbCmdVReceive);
       WHEN C_IB_RD_COMPL_TRANSACTION =>
         -- Receive Transaction
         ReceiveCompletition(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
         -- Show Transaction info
         ShowCommandInfo(LclIbCmdVReceive,"Upstream");
       WHEN OTHERS =>
         ASSERT false REPORT "IB_BFM: Unexcepted transaction on upstream port";
    END CASE;

  END LOOP;
END PROCESS;

-- Send Completitions --------------------------------------------------------
SEND_COMPLETITIONS: PROCESS
  VARIABLE i : integer;
BEGIN
  wait until (CLK'event and CLK='1');
  LOOP
    while (ComplFifo.Empty) loop
      wait until (CLK'event and CLK='1');
    end loop;
    getFifo(ComplDataCmdV);

    -- Memory delay
    for i in 0 to MEMORY_DELAY loop
      wait until (CLK'event and CLK='1');
    end loop;

    ComplReq.Req <= '1';
    WAIT ON ComplReq.ReqAck;
    ComplReq.Req <= '0';
    WAIT ON ComplReq.Ack;

  END LOOP;
END PROCESS;


END ARCHITECTURE IB_BFM_ARCH;

