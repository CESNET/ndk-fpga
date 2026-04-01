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

library std_developerskit;
use std_developerskit.std_iopak.all;       -- To_string

use work.math_pack.all;
use work.ib_pkg.all;
use work.ib_bfm_pkg.all;
use work.ib_bfm_rdy_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_BFM is
    generic (
        MEMORY_BASE_ADDR : std_logic_vector(63 downto 0) := X"FFFFFFFF00000000"; -- Memory Base ADDR
        MEMORY_SIZE      : integer := 1024;                                      -- Defaul 1024 Bytes
        MEMORY_DELAY     : integer := 10                                         -- Delay before sending completition
    );
    port (
        CLK          : in  std_logic;
        -- Internal Bus Interface
        IB           : inout t_internal_bus64
    );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_BFM_ARCH of IB_BFM is

    -- Request for completition
    signal          complreq               : IbCmdType := ('0', 'Z', 'Z');
    shared variable compldatacmdv          : IbCmdVType;

    -- Transactions
    shared variable lclibcmdv        : IbCmdVType;
    shared variable lclibcmdvreceive : IbCmdVType;

    -- Host Memory
    type            memorytype is array (0 to MEMORY_SIZE/8) of std_logic_vector(63 downto 0);
    shared variable memory : memorytype;

    -- Logging settings
    shared variable logtranscript : boolean := true;
    shared variable logfile       : boolean := false;

    -- Write Align Type
    type writealigntype is record

        Align    : integer;
        AlignReg : std_logic_vector(63 downto 0);
    end record;

    ----------------------------------------------------------------------------
    -- Completition FIFO for G2LR
    constant FIFO_LEN : integer := 256;
    type     fifotype is array (0 to FIFO_LEN-1) of IbCmdVType;
    type     completitionfifotype is record

        BeginPtr : integer;
        EndPtr   : integer;
        Items    : integer;
        Empty    : boolean;
        Fifo     : fifotype;
    end record;
    shared variable complfifo : completitionfifotype;

    -- -------------------------------------------------------------------------
    procedure initfifo is
    begin
        ComplFifo.EndPtr   := 0;
        ComplFifo.BeginPtr := 0;
        ComplFifo.Empty    := true;
        ComplFifo.Items    := 0;
    end procedure initfifo;

    -- -------------------------------------------------------------------------
    procedure insertfifo (
        input  :  in  IbCmdVType
    ) is
    begin
        ComplFifo.Fifo(ComplFifo.EndPtr) := input;
        ComplFifo.EndPtr                 := ComplFifo.EndPtr+1;
        ComplFifo.Items                  := ComplFifo.Items+1;
        if (ComplFifo.EndPtr = FIFO_LEN) then
            ComplFifo.EndPtr := 0;
        end if;
        ComplFifo.Empty  := false;
        assert (ComplFifo.EndPtr /= ComplFifo.BeginPtr or ComplFifo.Items = 0)
            report "IB_BFM: Completition fifo overflow";
    end procedure insertfifo;

    -- -------------------------------------------------------------------------
    procedure getfifo (
        output : inout IbCmdVType
    ) is
    begin
        if (not ComplFifo.Empty) then
            output             :=ComplFifo.Fifo(ComplFifo.BeginPtr);
            ComplFifo.BeginPtr := ComplFifo.BeginPtr + 1;
            if (ComplFifo.BeginPtr = FIFO_LEN) then
                ComplFifo.BeginPtr := 0;
            end if;
            ComplFifo.Items := ComplFifo.Items-1;
            ComplFifo.Empty := ComplFifo.BeginPtr = ComplFifo.EndPtr;
        end if;
    end procedure getfifo;

    -- -------------------------------------------------------------------------
    procedure to_bit_vector (
        input  :  in  std_logic_vector;
        output :  out bit_vector
    ) is
        variable i : integer;
    begin
        for i in 0 to input'high loop
            if (input(i) = '1') then
                output(i) := '1';
            else
                output(i) := '0';
            end if;
        end loop;
    end procedure to_bit_vector;

    -- -------------------------------------------------------------------------
    -- ShowCommand Info
    procedure showcommandinfo (
        cmdv :  in IbCmdVType;
        info : in string
    ) is
        variable srcaddr        : bit_vector(31 downto 0);
        variable dstaddr        : bit_vector(31 downto 0);
        variable localaddr      : bit_vector(31 downto 0);
        variable globaladdr     : bit_vector(63 downto 0);
        variable data           : bit_vector(63 downto 0);
        variable i              : integer;
        file     output         : ascii_text open write_mode is "STD_OUTPUT";
        file     outfile        : ascii_text open append_mode is "internal_bus.log";
    begin
        to_bit_vector(cmdV.Di.SrcAddr,    srcaddr);
        to_bit_vector(cmdV.Di.DstAddr,    dstaddr);
        to_bit_vector(cmdV.Di.LocalAddr,  localaddr);
        to_bit_vector(cmdV.Di.GlobalAddr, globaladdr);



        case cmdV.CmdOp is

            when LocalRead =>
                if (LogTranscript) then
                    fprint(output,"IB_BFM: %s Local2Local Read:  SrcAddr: 0x%s DstAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(srcaddr, "%x"), to_string(dstaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                if (LogFile) then
                    fprint(outfile,"IB_BFM: %s Local2Local Read:  SrcAddr: 0x%s DstAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(srcaddr, "%x"), to_string(dstaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;

            when LocalWrite =>
                if (LogTranscript) then
                    fprint(output,"IB_BFM: %s Local2Local Write: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(dstaddr, "%x"), to_string(srcaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                if (LogFile) then
                    fprint(outfile,"IB_BFM: %s Local2Local Write: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(dstaddr, "%x"), to_string(srcaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                i := 0;
                while i < cmdV.Di.Length loop
                    to_bit_vector(cmdV.Di.Data(i/8), data);
                    if (LogTranscript) then
                        fprint(output,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;
                    if (LogFile) then
                        fprint(outfile,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;

                    i := i+8;
                end loop;

            when Completition =>
                if (LogTranscript) then
                    fprint(output,"IB_BFM: %s Completition: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s LastFlag: %s\n",
                           info, to_string(dstaddr, "%x"), to_string(srcaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length), to_string(cmdV.Di.LastFlag));
                end if;
                if (LogFile) then
                    fprint(outfile,"IB_BFM: %s Completition: DstAddr: 0x%s SrcAddr: 0x%s Tag: %s Length: %s LastFlag: %s\n",
                           info, to_string(dstaddr, "%x"), to_string(srcaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length), to_string(cmdV.Di.LastFlag));
                end if;
                i := 0;
                while i < cmdV.Di.Length loop
                    to_bit_vector(cmdV.Di.Data(i/8), data);
                    if (LogTranscript) then
                        fprint(output,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;
                    if (LogFile) then
                        fprint(outfile,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;
                    i := i+8;
                end loop;

            when G2LR =>
                if (LogTranscript) then
                    fprint(output,"IB_BFM: %s Global2Local Read:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(globaladdr, "%x"), to_string(localaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                if (LogFile) then
                    fprint(outfile,"IB_BFM: %s Global2Local Read:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(globaladdr, "%x"), to_string(localaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;

            when L2GW =>
                if (LogTranscript) then
                    fprint(output,"IB_BFM: %s Local2Global Write:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(globaladdr, "%x"), to_string(localaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                if (LogFile) then
                    fprint(outfile,"IB_BFM: %s Local2Global Write:  GlobalAddr: 0x%s LocalAddr: 0x%s Tag: %s Length: %s\n",
                           info, to_string(globaladdr, "%x"), to_string(localaddr, "%x"),to_string(cmdV.Di.Tag),
                           to_string(cmdV.Di.Length));
                end if;
                i := 0;
                while i < cmdV.Di.Length loop
                    to_bit_vector(cmdV.Di.Data(i/8), data);
                    if (LogTranscript) then
                        fprint(output,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;
                    if (LogFile) then
                        fprint(outfile,"        DATA: 0x%s\n", to_string(data, "%x"));
                    end if;
                    i := i+8;
                end loop;

            when others =>

        end case;
    end procedure showcommandinfo;

    -- -------------------------------------------------------------------------
    -- Init Align
    procedure aligninit (
        align      :  in integer;
        writealign : inout writealigntype
    ) is
    begin
        WriteAlign.Align    := align;
        WriteAlign.AlignReg := X"0000000000000000";
    end procedure aligninit;

    -- -------------------------------------------------------------------------
    -- GetWriteCount
    function getwritecount (Align  :  in integer;
        Length :  in integer) return integer is
        variable plus : integer;
    begin
        if (((Length+Align) mod 8) > 0) then
            plus := 1;
        else
            plus := 0;
        end if;
        return (Length+Align)/8 + plus;
    end function;

    -- -------------------------------------------------------------------------
    -- GetWriteData
    procedure getwritedata (
        datain         : in std_logic_vector(63 downto 0);
        signal dataout : out std_logic_vector(63 downto 0);
        writealign     : inout writealigntype
    ) is
        variable i : integer;
        variable j : integer;
    begin
        if (WriteAlign.Align = 0) then
            dataout <= datain;
        else
            j := 0;
            for i in WriteAlign.Align*8-1 downto 0 loop
                dataout(i) <= WriteAlign.AlignReg(64-(WriteAlign.Align*8)+i);
            end loop;
            for i in WriteAlign.Align*8 to 63 loop
                dataout(i) <= datain(j);
                j          := j+1;
            end loop;
            WriteAlign.AlignReg := datain;
        end if;
    end procedure getwritedata;


    -- -------------------------------------------------------------------------
    -- Generate LocalRead Transaction
    procedure localread (
        variable trans     :  in IbCmdVType;
        signal   clk       :  in std_logic;
        signal   data      : out std_logic_vector(63 downto 0);
        signal   sop_n     : out std_logic;
        signal   eop_n     : out std_logic;
        signal   src_rdy_n : out std_logic;
        signal   dst_rdy_n :  in std_logic
    ) is
    begin

        data      <= trans.Di.SrcAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                     '0' & C_IB_L2LR_TRANSACTION & conv_std_logic_vector(trans.Di.Length,12);
        src_rdy_n <= '0';
        sop_n     <= '0';
        eop_n     <= '1';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');
        data      <= X"00000000" & trans.Di.DstAddr;
        src_rdy_n <= '0';
        sop_n     <= '1';
        eop_n     <= '0';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');
        sop_n     <= '1';
        eop_n     <= '1';
        src_rdy_n <= '1';
    end procedure localread;

    -- -------------------------------------------------------------------------
    -- Generate LocalWrite Transaction
    procedure localwrite (
        variable trans     :  in IbCmdVType;
        signal   clk       :  in std_logic;
        signal   data      : out std_logic_vector(63 downto 0);
        signal   sop_n     : out std_logic;
        signal   eop_n     : out std_logic;
        signal   src_rdy_n : out std_logic;
        signal   dst_rdy_n :  in std_logic
    ) is
        variable i           : integer;
        variable len         : integer;
        variable aux_len     : integer;
        variable count       : integer;
        variable writealign  : writealigntype;
    begin
        -- Set maximum length to 0 in header
        if (trans.Di.Length = 4096) then
            aux_len := 0;
        else
            aux_len := trans.Di.Length;
        end if;

        -- Send HDR0
        data      <= trans.Di.DstAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                     '0' & C_IB_L2LW_TRANSACTION & conv_std_logic_vector(aux_len,12);
        src_rdy_n <= '0';
        sop_n     <= '0';
        eop_n     <= '1';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');

        -- Send HDR1
        data      <= X"00000000" & trans.Di.SrcAddr;
        src_rdy_n <= '0';
        sop_n     <= '1';
        eop_n     <= '1';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');

        -- Send DATA
        AlignInit(conv_integer(trans.Di.DstAddr(2 downto 0)), writealign);
        len   := trans.Di.Length;
        count := GetWriteCount(conv_integer(trans.Di.DstAddr(2 downto 0)),conv_integer(trans.Di.Length));
        for i in 0 to count-1 loop
            if (len > 0) then
                GetWriteData(trans.Di.Data(i), data, writealign);
            else
                GetWriteData(X"0000000000000000", data, writealign);
            end if;
            src_rdy_n <= '0';
            sop_n     <= '1';
            if (i = (count-1)) then
                eop_n   <= '0';
            else
                eop_n   <= '1';
            end if;
            wait until (clk'event and clk = '1' and dst_rdy_n = '0');
            len := len - 8;
        end loop;

        sop_n     <= '1';
        eop_n     <= '1';
        src_rdy_n <= '1';
    end procedure localwrite;

    -- -------------------------------------------------------------------------
    -- Generate Completition Transaction
    procedure completition (
        variable trans     :  in IbCmdVType;
        signal   clk       :  in std_logic;
        signal   data      : out std_logic_vector(63 downto 0);
        signal   sop_n     : out std_logic;
        signal   eop_n     : out std_logic;
        signal   src_rdy_n : out std_logic;
        signal   dst_rdy_n :  in std_logic
    ) is
        variable i          : integer;
        variable len        : integer;
        variable count      : integer;
        variable writealign : writealigntype;
    begin

        -- Send HDR0
        data      <= trans.Di.DstAddr & conv_std_logic_vector(trans.Di.Tag, 16) &
                     trans.Di.LastFlag & C_IB_RD_COMPL_TRANSACTION & conv_std_logic_vector(trans.Di.Length,12);
        src_rdy_n <= '0';
        sop_n     <= '0';
        eop_n     <= '1';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');

        -- Send HDR1
        data      <= X"00000000" & trans.Di.SrcAddr;
        src_rdy_n <= '0';
        sop_n     <= '1';
        eop_n     <= '1';
        wait until (clk'event and clk = '1' and dst_rdy_n = '0');

        -- Send DATA
        AlignInit(conv_integer(trans.Di.DstAddr(2 downto 0)),writealign);
        len   := trans.Di.Length;
        count := GetWriteCount(conv_integer(trans.Di.DstAddr(2 downto 0)),conv_integer(trans.Di.Length));
        for i in 0 to count-1 loop
            if (len > 0) then
                GetWriteData(trans.Di.Data(i), data, writealign);
            else
                GetWriteData(X"0000000000000000", data, writealign);
            end if;
            src_rdy_n <= '0';
            sop_n     <= '1';
            if (i = (count-1)) then
                eop_n   <= '0';
            else
                eop_n   <= '1';
            end if;
            wait until (clk'event and clk = '1' and dst_rdy_n = '0');
            len := len - 8;
        end loop;

        sop_n     <= '1';
        eop_n     <= '1';
        src_rdy_n <= '1';
    end procedure completition;

    -- -------------------------------------------------------------------------
    -- Receive Completition Transaction
    procedure receivecompletition (
        signal clk       :  in std_logic;
        signal data      :  in std_logic_vector(63 downto 0);
        signal sop_n     :  in std_logic;
        signal eop_n     :  in std_logic;
        signal src_rdy_n :  in std_logic;
        signal dst_rdy_n :  in std_logic
    ) is
        variable i     : integer;
    begin
        -- Receive Header 1
        LclIbCmdVReceive.CmdOp       := Completition;
        LclIbCmdVReceive.Di.DstAddr  := data(63 downto 32);
        LclIbCmdVReceive.Di.Tag      := conv_integer(data(31 downto 16));
        LclIbCmdVReceive.Di.LastFlag := data(15);
        LclIbCmdVReceive.Di.Length   := conv_integer(data(11 downto  0));
        wait until (clk'event and clk = '1' and src_rdy_n = '0' and dst_rdy_n = '0');
        -- Receive Header2
        LclIbCmdVReceive.Di.SrcAddr  := data(63 downto 32);
        -- Receive Data
        i                            := 0;
        while i < LclIbCmdVReceive.Di.Length loop
            wait until (clk'event and clk = '1' and src_rdy_n = '0' and dst_rdy_n = '0');
            LclIbCmdVReceive.Di.Data(i/8) := data;
            i                             := i+8;
        end loop;
    end procedure receivecompletition;

    -- -------------------------------------------------------------------------
    -- Receive G2LR Transaction
    procedure receiveg2lr (
        signal clk       :  in std_logic;
        signal data      :  in std_logic_vector(63 downto 0);
        signal sop_n     :  in std_logic;
        signal eop_n     :  in std_logic;
        signal src_rdy_n :  in std_logic;
        signal dst_rdy_n :  in std_logic
    ) is
    begin
        -- Receive Header 1
        LclIbCmdVReceive.CmdOp                       := G2LR;
        LclIbCmdVReceive.Di.GlobalAddr(31 downto 0)  := data(63 downto 32);
        LclIbCmdVReceive.Di.Tag                      := conv_integer(data(31 downto 16));
        if (conv_integer(data(11 downto 0)) = 0) then
            LclIbCmdVReceive.Di.Length                 := 4096;
        else
            LclIbCmdVReceive.Di.Length                 := conv_integer(data(11 downto  0));
        end if;
        wait until (clk'event and clk = '1' and src_rdy_n = '0' and dst_rdy_n = '0');
        -- Receive Header2
        LclIbCmdVReceive.Di.GlobalAddr(63 downto 32) := data(63 downto 32);
        LclIbCmdVReceive.Di.LocalAddr                := data(31 downto 0);
    end procedure receiveg2lr;

    -- -------------------------------------------------------------------------
    -- Receive L2GW Transaction
    procedure receivel2gw (
        signal clk       :  in std_logic;
        signal data      :  in std_logic_vector(63 downto 0);
        signal sop_n     :  in std_logic;
        signal eop_n     :  in std_logic;
        signal src_rdy_n :  in std_logic;
        signal dst_rdy_n :  in std_logic
    ) is
        variable i     : integer;
    begin
        -- Receive Header 1
        LclIbCmdVReceive.CmdOp                       := L2GW;
        LclIbCmdVReceive.Di.GlobalAddr(31 downto 0)  := data(63 downto 32);
        LclIbCmdVReceive.Di.Tag                      := conv_integer(data(31 downto 16));
        if (conv_integer(data(11 downto 0)) = 0) then
            LclIbCmdVReceive.Di.Length                 := 4096;
        else
            LclIbCmdVReceive.Di.Length                 := conv_integer(data(11 downto  0));
        end if;
        wait until (clk'event and clk = '1' and src_rdy_n = '0' and dst_rdy_n = '0');
        -- Receive Header2
        LclIbCmdVReceive.Di.GlobalAddr(63 downto 32) := data(63 downto 32);
        LclIbCmdVReceive.Di.LocalAddr                := data(31 downto 0);
        -- Receive Data
        i                                            := 0;
        while i < LclIbCmdVReceive.Di.Length loop
            wait until (clk'event and clk = '1' and src_rdy_n = '0' and dst_rdy_n = '0');
            LclIbCmdVReceive.Di.Data(i/8) := data;
            i                             := i+8;
        end loop;
    end procedure receivel2gw;


    -- -------------------------------------------------------------------------
    -- Load Host Memory Data
    procedure inithostmemory is
        variable i     : integer;
    begin
        -- Init Memory with data
        i := 0;
        while i < LclIbCmdV.Di.Length loop
            Memory((LclIbCmdV.Di.MemAddr+i)/8) := LclIbCmdV.Di.Data(i/8);
            i                                  := i+8;
        end loop;

        while (LclIbCmdV.Di.MemAddr+i) < MEMORY_SIZE loop
            Memory((LclIbCmdV.Di.MemAddr+i)/8) := X"0000000000000000";
            i                                  := i+8;
        end loop;
    end procedure inithostmemory;

    -- -------------------------------------------------------------------------
    -- Show Host Memory
    procedure showhostmemory is
        variable data       : bit_vector(63 downto 0);
        variable i          : integer;
        file     output     : ascii_text open write_mode is "STD_OUTPUT";
        file     outfile    : ascii_text open append_mode is "internal_bus.log";
    begin
        if (LogTranscript) then
            fprint(output,"IB_BFM: Host Memory Content\n");
            -- Show Content
            for i in 0 to MEMORY_SIZE/8 loop
                to_bit_vector(Memory(i), data);
                fprint(output,"        DATA: 0x%s\n", to_string(data, "%x"));
            end loop;
        end if;
        if (LogFile) then
            fprint(outfile,"IB_BFM: Host Memory Content\n");
            -- Show Content
            for i in 0 to MEMORY_SIZE/8 loop
                to_bit_vector(Memory(i), data);
                fprint(outfile,"        DATA: 0x%s\n", to_string(data, "%x"));
            end loop;
        end if;
    end procedure showhostmemory;

    -- -------------------------------------------------------------------------
    -- Process L2GW Transaction (Save Transaction into memory)
    procedure processl2gw (
        trans :  in IbCmdVType
    ) is
        variable dstaddr : std_logic_vector(63 downto 0);
        variable start   : integer;
        variable i       : integer;
        variable j       : integer;
    begin
        dstaddr := trans.Di.GlobalAddr - MEMORY_BASE_ADDR;
        assert (dstaddr >= 0 and dstaddr+trans.Di.Length <= MEMORY_SIZE)
            report "L2GW outside of Host Memory address space";

        start := conv_integer(DstAddr(31 downto 0));
        j     := 0;
        for i in start to (start+trans.Di.Length)-1 loop
            Memory(i/8)( (i mod 8)*8+7 downto (i mod 8)*8) := trans.Di.Data(j/8)((j mod 8)*8+7 downto (j mod 8)*8);
            j                                              := j+1;
        end loop;
    end procedure processl2gw;

    -- -------------------------------------------------------------------------
    -- Process G2LR Transaction (Save Transaction into Completition FIFO)
    procedure processg2lr (
        trans :  in IbCmdVType
    ) is
        variable dstaddr : std_logic_vector(63 downto 0);
        variable start   : integer;
        variable i       : integer;
        variable j       : integer;
        variable compl   : IbCmdVType;
    begin
        dstaddr := trans.Di.GlobalAddr - MEMORY_BASE_ADDR;
        assert (dstaddr >= 0 and dstaddr+trans.Di.Length <= MEMORY_SIZE)
            report "L2GW outside of Host Memory address space";

        compl.CmdOp       := Completition;
        compl.Di.DstAddr  := trans.Di.LocalAddr;
        compl.Di.SrcAddr  := X"FFFFFFFF";
        compl.Di.Tag      := trans.Di.Tag;
        compl.Di.Length   := trans.Di.Length;
        compl.Di.LastFlag := '1';

        -- Get Data from memory into field
        start := conv_integer(DstAddr(31 downto 0));
        j     := 0;
        for i in start to (start+trans.Di.Length)-1 loop
            compl.Di.Data(j/8)((j mod 8)*8+7 downto (j mod 8)*8) := Memory(i/8)((i mod 8)*8+7 downto (i mod 8)*8);
            j                                                    := j+1;
        end loop;
        -- Insert Completition Into Fifo
        insertFifo(compl);
    end procedure processg2lr;

begin


    -- Send Packet Process --------------------------------------------------------
    send_packets : process
        file     log_file  : text;
    begin
        IB.DOWN.DATA      <= (others => '0');
        IB.DOWN.SOP_N     <= '1';
        IB.DOWN.EOP_N     <= '1';
        IB.DOWN.SRC_RDY_N <= '1';

        IbCmd.Ack         <= '0';
        ComplReq.Ack      <= '0';
        IbCmd.ReqAck      <= '0';
        ComplReq.ReqAck   <= '0';

        loop
            -- Get Command
            while (IbCmd.Req = '0' and ComplReq.Req = '0') loop
                wait until (IbCmd.Req = '1' or ComplReq.Req = '1');
            end loop;

            if (IbCmd.Req = '1') then
                -- Send Request Acknowledge
                IbCmd.ReqAck <= NOT(IbCmd.ReqAck);
                -- Wait for Reqest Deasert
                wait on IbCmd.Req;

                ReadIbCmdV(lclibcmdv);
                showcommandinfo(lclibcmdv,"Downstream");
                -- Process Command
                case LclIbCmdV.CmdOp is
                    when LocalRead      =>
                        localread(lclibcmdv, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
                    when LocalWrite     =>
                        localwrite(lclibcmdv, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
                    when Completition   =>
                        completition(lclibcmdv, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);
                    when InitMemory     =>
                        inithostmemory;
                    when InitMemoryFromAddr =>
                        inithostmemory;
                    when ShowMemory     =>
                        showhostmemory;
                    when TranscriptLogging =>
                        logtranscript := LclIbCmdV.Di.Enable;
                    when FileLogging       =>
                        logfile       := LclIbCmdV.Di.Enable;
                        if (logfile) then
                            file_open(log_file, "internal_bus.log", WRITE_MODE);
                            file_close(log_file);
                        end if;
                    when others            =>
                end case;

                -- Send Command done
                IbCmd.Ack <= NOT(IbCmd.Ack);
            end if;

            if (ComplReq.Req = '1') then
                -- Send Request Acknowledge
                ComplReq.ReqAck <= NOT(ComplReq.ReqAck);
                -- Wait for Reqest Deasert
                wait on ComplReq.Req;

                showcommandinfo(compldatacmdv,"Downstream");
                completition(compldatacmdv, CLK, IB.DOWN.DATA, IB.DOWN.SOP_N, IB.DOWN.EOP_N, IB.DOWN.SRC_RDY_N, IB.DOWN.DST_RDY_N);

                -- Send Command done
                ComplReq.Ack <= NOT(ComplReq.Ack);
            end if;

        end loop;
    end process;

    -- Drive DST_RDY_N ---------------------------------------------------------------
    drive_dst_rdy_n : process
    begin
        loop
            DriveDstRdyN(CLK, IB.UP.DST_RDY_N);
        end loop;
    end process;


    -- Receive Packet Process --------------------------------------------------------
    receive_packets : process
    begin
        initfifo; -- Init Completition fifo
        --  IB.UP.DST_RDY_N <= '0'; Replaced by DRIVE_DST_RDY_N process
        loop
            wait until (CLK'event and CLK = '1' and IB.UP.SRC_RDY_N = '0' and IB.UP.SOP_N = '0' and IB.UP.DST_RDY_N = '0');

            case IB.UP.DATA(14 downto 12) is
                when C_IB_L2GW_TRANSACTION =>
                    -- Receive Transaction
                    receivel2gw(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
                    -- Show Transaction info
                    showcommandinfo(lclibcmdvreceive,"Upstream");
                    -- Store transaction data into memory
                    processl2gw(lclibcmdvreceive);
                when C_IB_G2LR_TRANSACTION =>
                    -- Receive Transaction
                    receiveg2lr(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
                    -- Show Transaction info
                    showcommandinfo(lclibcmdvreceive,"Upstream");
                    -- Store Reqest into fifo
                    processg2lr(lclibcmdvreceive);
                when C_IB_RD_COMPL_TRANSACTION =>
                    -- Receive Transaction
                    receivecompletition(CLK, IB.UP.DATA, IB.UP.SOP_N, IB.UP.EOP_N, IB.UP.SRC_RDY_N, IB.UP.DST_RDY_N);
                    -- Show Transaction info
                    showcommandinfo(lclibcmdvreceive,"Upstream");
                when others =>
                    assert false
                        report "IB_BFM: Unexcepted transaction on upstream port";
            end case;

        end loop;
    end process;

    -- Send Completitions --------------------------------------------------------
    send_completitions : process
        variable i : integer;
    begin
        wait until (CLK'event and CLK = '1');
        loop
            while (ComplFifo.Empty) loop
                wait until (CLK'event and CLK = '1');
            end loop;
            getfifo(compldatacmdv);

            -- Memory delay
            for i in 0 to MEMORY_DELAY loop
                wait until (CLK'event and CLK = '1');
            end loop;

            ComplReq.Req <= '1';
            wait on ComplReq.ReqAck;
            ComplReq.Req <= '0';
            wait on ComplReq.Ack;

        end loop;
    end process;


end architecture;

