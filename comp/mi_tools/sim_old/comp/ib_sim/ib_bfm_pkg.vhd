-- storage_init_pkg.vhd: Storage Init PKG
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
use IEEE.std_logic_arith.all;
use IEEE.std_logic_textio.all;
use IEEE.numeric_std.all;
use std.textio.all;

-- ----------------------------------------------------------------------------
--                        Internal Bus BFM Package
-- ----------------------------------------------------------------------------
package ib_bfm_pkg is

    constant MAX_TRANS_LENGTH : integer := 4095;
    constant MAX_WRITE_LENGTH : integer := 4096;
    constant MAX_INIT_DATA    : integer := 4096;


    -----------------------------------------------------------------------------
    -- DATA TYPES
    -----------------------------------------------------------------------------
    -- Internal Bus Operation Type
    type iboptype is (
        LOCALREAD, LOCALWRITE, COMPLETITION, G2LR, L2GW, FILELOGGING, TRANSCRIPTLOGGING,
        INITMEMORY, INITMEMORYFROMADDR, SHOWMEMORY
    );

    -- File Name Type
    type filenametype is record
        Len   : integer;
        Arr   : string(1 to 256);
    end record;

    type datatype is array (0 to MAX_INIT_DATA/8) of std_logic_vector(63 downto 0);

    -- Operation parameters
    type dicmdtype is record
        SrcAddr        : std_logic_vector(31 downto 0); -- Source Address
        DstAddr        : std_logic_vector(31 downto 0); -- Destination Address
        LocalAddr      : std_logic_vector(31 downto 0); -- Local Address (for GlobalTransactions)
        GlobalAddr     : std_logic_vector(63 downto 0); -- Global Address (for GlobalTransactions)
        Length         : integer;                       -- Length
        Tag            : integer;                       -- Tag
        Data           : DataType;                      -- Data
        LastFlag       : std_logic;                     -- Completition Last Flag
        Enable         : boolean;
        FileName       : FileNameType;
        MemAddr        : integer;
    end record;

    -- Command record
    type ibcmdvtype is record

        CmdOp     : IbOpType;  -- Operation
        Di        : DiCmdType; -- Operation input parameters
    end record;

    -- Command REQ/ACK record
    type ibcmdtype is record

        Req      : std_logic;
        ReqAck   : std_logic;
        Ack      : std_logic;
    end record;

    ----------------------------------------------------------------------------
    -- SIGNAL FOR SETTINGS BFM REQUESTS
    ----------------------------------------------------------------------------
    signal ibcmd : IbCmdType := ('0', 'Z', 'Z');


    ----------------------------------------------------------------------------
    -- BFM FUNCTIONS
    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Functions is called by IB BFM model to obtain command parameters
    procedure readibcmdv (
        variable lclibcmdv : out IbCmdVType
    );

    ----------------------------------------------------------------------------
    -- Functions is called by IB BFM model to return results
    procedure writeibcmdv (
        variable lclibcmdv  : in IbCmdVType
    );

    -----------------------------------------------------------------------------
    -- Converts string type into the FileNameType
    function convfilename (FileName : string) return FileNameType;

    -----------------------------------------------------------------------------
    -- Converts FileNameType into the string
    function convfilename (FileName : FileNameType) return string;


    ----------------------------------------------------------------------------
    -- USER FUNCTIONS
    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Send Local Read Transaction
    procedure sendlocalread (
        constant srcaddr  : in std_logic_vector(31 downto 0); -- Address from where are data readed
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination address of completition transaction
        constant length   : in integer;                       -- Number of bytes to be readed
        constant tag      : in integer;                       -- Transaction Tag
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Local Write Transaction
    procedure sendlocalwrite (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Local Write Transaction with Data from File
    procedure sendlocalwritefile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Local Write Transaction
    procedure sendlocalwrite32 (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(31 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Local Write Transaction with Data from File
    procedure sendlocalwritefile32 (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (32 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Completition Transaction
    procedure sendcompletition (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Completition Transaction with Data from File
    procedure sendcompletitionfile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Not Last Completition Transaction (op_done is not generated)
    procedure sendnotlastcompletition (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Send Not Last Completition Transaction with Data from File (op_done is not generated)
    procedure sendnotlastcompletitionfile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Enable Transcript Logging
    procedure settranscriptlogging (
        constant enable   : in boolean;                       -- Enable/Disable
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Enable File Logging
    procedure setfilelogging (
        constant enable   : in boolean;                       -- Enable/Disable
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

    -----------------------------------------------------------------------
    -- Init HostPC Memory
    procedure initmemory (
        constant length   : in integer;                       -- Length of writen data
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );
    -----------------------------------------------------------------------
    -- Init HostPC Memory Starting From Given Address
    procedure initmemoryfromaddr (
        constant length   : in integer;                       -- Length of writen data
        constant address  : in integer;                       -- Where to write data
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );
    -----------------------------------------------------------------------
    -- Show content of Memory
    procedure showmemory (
        signal   ibcmd    : inout IbCmdType                   -- Command record
    );

end package;



-- ----------------------------------------------------------------------------
--                      Internal Bus BFM Package BODY
-- ----------------------------------------------------------------------------
package body ib_bfm_pkg is

    -----------------------------------------------------------------------------
    -- Command shared variable
    shared variable ibcmdv : IbCmdVType;

    -----------------------------------------------------------------------------
    -- Functions is called by IB BFM model to obtain command parameters
    procedure readibcmdv (
        variable lclibcmdv : out IbCmdVType
    ) is
    begin
        LclIbCmdV := IbCmdV;
    end procedure readibcmdv;

    -----------------------------------------------------------------------------
    -- Functions is called by IB BFM model to return results
    procedure writeibcmdv (
        variable lclibcmdv  : in IbCmdVType
    ) is
    begin
        IbCmdV := lclibcmdv;
    end procedure writeibcmdv;

    -----------------------------------------------------------------------------
    -- Converts string type into the FileNameType
    function convfilename (FileName : string) return FileNameType is
        variable result : FileNameType;
    begin
        result.Len                  := FileName'length;
        result.Arr(1 to result.len) := FileName;
        return result;
    end function;

    -----------------------------------------------------------------------------
    -- Converts FileNameType into the string
    function convfilename (FileName : FileNameType) return string is
    begin
        return FileName.arr(1 to FileName.len);
    end function;

    -- ----------------------------------------------------------------
    -- Count Number of lines in file
    function filelinecount (FileName : in string) return integer is
        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable data         : std_logic_vector(63 downto 0);
        variable i            : integer;
    begin
        i := 0;
        file_open(in_file, FileName, READ_MODE);
        while not (endfile(in_file)) loop
            readline(in_file, in_line);
            i := i+1;
        end loop;
        file_close(in_file);
        return i;
    end function;

    -----------------------------------------------------------------------------
    -- Send Local Read Transaction
    procedure sendlocalread (
        constant srcaddr  : in std_logic_vector(31 downto 0); -- Address from where are data readed
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination address of completition transaction
        constant length   : in integer;                       -- Number of bytes to be readed
        constant tag      : in integer;                       -- Transaction Tag
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        assert (length <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp      := LocalRead;
        IbCmdV.Di.SrcAddr := srcaddr;
        IbCmdV.Di.DstAddr := dstaddr;
        IbCmdV.Di.Length  := length;
        IbCmdV.Di.Tag     := tag;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req         <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req         <= '0';
        wait on IbCmd.Ack;
    end procedure sendlocalread;

    -----------------------------------------------------------------------------
    -- Send Local Write Transaction
    procedure sendlocalwrite (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        assert (length <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp      := LocalWrite;
        IbCmdV.Di.SrcAddr := srcaddr;
        IbCmdV.Di.DstAddr := dstaddr;
        IbCmdV.Di.Length  := length;
        IbCmdV.Di.Tag     := tag;
        IbCmdV.Di.Data(0) := data;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req         <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req         <= '0';
        wait on IbCmd.Ack;
    end procedure sendlocalwrite;

    -----------------------------------------------------------------------------
    -- Send Local Write File Transaction
    procedure sendlocalwritefile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is

        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
        variable j            : integer;
        variable split_cnt    : integer;
        variable split_len    : integer;
    begin
        if (length = 0) then
            len := FileLineCount(filename)*8;
        else
            len := length;
        end if;

        if (len <= MAX_WRITE_LENGTH) then
            IbCmdV.CmdOp       := LocalWrite;
            IbCmdV.Di.SrcAddr  := srcaddr;
            IbCmdV.Di.DstAddr  := dstaddr;
            IbCmdV.Di.Length   := len;
            IbCmdV.Di.Tag      := tag;

            file_open(in_file, filename, READ_MODE);
            i := 0;
            while (i < len) loop
                readline(in_file, in_line);
                hread(in_line, IbCmdV.Di.Data(i/8), readflag);
                assert readflag
                    report "SendLocalWriteFile read error"
                    severity ERROR;
                i := i+8;
            end loop;
            file_close(in_file);
            -- Req toggles each time we want the BFM to do a new check.
            IbCmd.Req <= '1';
            wait on IbCmd.ReqAck;
            IbCmd.Req <= '0';
            wait on IbCmd.Ack;

        else -- Split transactions
            file_open(in_file, filename, READ_MODE);
            split_cnt := (len / MAX_WRITE_LENGTH);
            if (len > (MAX_WRITE_LENGTH*split_cnt)) then
                split_cnt := split_cnt+1;
            end if;

            i := 0;
            while (split_cnt > 0) loop
                if (len > MAX_WRITE_LENGTH) then
                    split_len := MAX_WRITE_LENGTH;
                else
                    split_len := len;
                end if;
                IbCmdV.CmdOp       := LocalWrite;
                IbCmdV.Di.SrcAddr  := srcaddr;
                IbCmdV.Di.DstAddr  := dstaddr+(i*MAX_WRITE_LENGTH);
                IbCmdV.Di.Length   := split_len;
                IbCmdV.Di.Tag      := tag;

                j := 0;
                while (j < split_len) loop
                    readline(in_file, in_line);
                    hread(in_line, IbCmdV.Di.Data(j/8), readflag);
                    assert readflag
                        report "SendLocalWriteFile read error"
                        severity ERROR;
                    j := j+8;
                end loop;


                i         := i+1;
                split_cnt := split_cnt-1;
                len       := len-MAX_WRITE_LENGTH;
                -- Req toggles each time we want the BFM to do a new check.
                IbCmd.Req <= '1';
                wait on IbCmd.ReqAck;
                IbCmd.Req <= '0';
                wait on IbCmd.Ack;
            end loop;
            file_close(in_file);
        end if;
    end procedure sendlocalwritefile;

    -----------------------------------------------------------------------------
    -- Send Local Write Transaction
    procedure sendlocalwrite32 (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(31 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        assert (length <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp      := LocalWrite;
        IbCmdV.Di.SrcAddr := srcaddr;
        IbCmdV.Di.DstAddr := dstaddr;
        IbCmdV.Di.Length  := length;
        IbCmdV.Di.Tag     := tag;
        IbCmdV.Di.Data(0) := X"00000000" & data;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req         <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req         <= '0';
        wait on IbCmd.Ack;
    end procedure sendlocalwrite32;

    -----------------------------------------------------------------------------
    -- Send Local Write File Transaction
    procedure sendlocalwritefile32 (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (32 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is

        file     in_file      : text;
        variable in_line      : line;
        variable data32a      : std_logic_vector(31 downto 0);
        variable data32b      : std_logic_vector(31 downto 0);
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
        variable j            : integer;
        variable split_cnt    : integer;
        variable split_len    : integer;

    begin
        if (length = 0) then
            len := FileLineCount(filename)*4;
        else
            len := length;
        end if;
        if (len <= MAX_WRITE_LENGTH) then
            IbCmdV.CmdOp       := LocalWrite;
            IbCmdV.Di.SrcAddr  := srcaddr;
            IbCmdV.Di.DstAddr  := dstaddr;
            IbCmdV.Di.Length   := len;
            IbCmdV.Di.Tag      := tag;

            file_open(in_file, filename, READ_MODE);
            i := 0;
            while (i < len) loop
                readline(in_file, in_line);
                hread(in_line, data32a, readflag);
                assert readflag
                    report "SendLocalWriteFile32 read error"
                    severity ERROR;
                if ((i + 4) < len) then
                    readline(in_file, in_line);
                    hread(in_line, data32b, readflag);
                    assert readflag
                        report "SendLocalWriteFile32 read error"
                        severity ERROR;
                else
                    data32b :=X"00000000";
                end if;
                IbCmdV.Di.Data(i/8) := data32b&data32a;
                i                   := i+8;
            end loop;
            file_close(in_file);

            -- Req toggles each time we want the BFM to do a new check.
            IbCmd.Req <= '1';
            wait on IbCmd.ReqAck;
            IbCmd.Req <= '0';
            wait on IbCmd.Ack;
        else
            file_open(in_file, filename, READ_MODE);
            split_cnt := (len / MAX_WRITE_LENGTH);
            if (len > (MAX_WRITE_LENGTH*split_cnt)) then
                split_cnt := split_cnt+1;
            end if;

            i := 0;
            while (split_cnt > 0) loop
                if (len > MAX_WRITE_LENGTH) then
                    split_len := MAX_WRITE_LENGTH;
                else
                    split_len := len;
                end if;
                IbCmdV.CmdOp       := LocalWrite;
                IbCmdV.Di.SrcAddr  := srcaddr;
                IbCmdV.Di.DstAddr  := dstaddr+(i*MAX_WRITE_LENGTH);
                IbCmdV.Di.Length   := split_len;
                IbCmdV.Di.Tag      := tag;

                j := 0;
                while (j < split_len) loop
                    readline(in_file, in_line);
                    hread(in_line, data32a, readflag);
                    assert readflag
                        report "SendLocalWriteFile32 read error"
                        severity ERROR;
                    if ((j + 4) < len) then
                        readline(in_file, in_line);
                        hread(in_line, data32b, readflag);
                        assert readflag
                            report "SendLocalWriteFile32 read error"
                            severity ERROR;
                    else
                        data32b :=X"00000000";
                    end if;
                    IbCmdV.Di.Data(j/8) := data32b&data32a;
                    j                   := j+8;
                end loop;


                i         := i+1;
                split_cnt := split_cnt-1;
                len       := len-MAX_WRITE_LENGTH;
                -- Req toggles each time we want the BFM to do a new check.
                IbCmd.Req <= '1';
                wait on IbCmd.ReqAck;
                IbCmd.Req <= '0';
                wait on IbCmd.Ack;
            end loop;
            file_close(in_file);

        end if;
    end procedure sendlocalwritefile32;

    -----------------------------------------------------------------------
    -- Send Completition Transaction
    procedure sendcompletition (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        assert (length <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp       := Completition;
        IbCmdV.Di.SrcAddr  := srcaddr;
        IbCmdV.Di.DstAddr  := dstaddr;
        IbCmdV.Di.Length   := length;
        IbCmdV.Di.Tag      := tag;
        IbCmdV.Di.Data(0)  := data;
        IbCmdV.Di.LastFlag := '1';
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req          <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req          <= '0';
        wait on IbCmd.Ack;
    end procedure sendcompletition;


    -----------------------------------------------------------------------
    -- Send Completition Transaction with Data from File
    procedure sendcompletitionfile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
    begin
        if (length = 0) then
            len := FileLineCount(filename)*8;
        else
            len := length;
        end if;
        assert (len <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp       := Completition;
        IbCmdV.Di.SrcAddr  := srcaddr;
        IbCmdV.Di.DstAddr  := dstaddr;
        IbCmdV.Di.Length   := len;
        IbCmdV.Di.Tag      := tag;
        IbCmdV.Di.LastFlag := '1';
        file_open(in_file, filename, READ_MODE);
        i                  := 0;
        while (i < len) loop
            readline(in_file, in_line);
            hread(in_line, IbCmdV.Di.Data(i/8), readflag);
            assert readflag
                report "SendCompletitionFile read error"
                severity ERROR;
            i := i+8;
        end loop;
        file_close(in_file);

        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req <= '0';
        wait on IbCmd.Ack;
    end procedure sendcompletitionfile;

    -----------------------------------------------------------------------
    -- Send Not Last Completition Transaction (op_done is not generated)
    procedure sendnotlastcompletition (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant data     : in std_logic_vector(63 downto 0); -- Data to be writen
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        assert (length <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp       := Completition;
        IbCmdV.Di.SrcAddr  := srcaddr;
        IbCmdV.Di.DstAddr  := dstaddr;
        IbCmdV.Di.Length   := length;
        IbCmdV.Di.Tag      := tag;
        IbCmdV.Di.Data(0)  := data;
        IbCmdV.Di.LastFlag := '0';
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req          <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req          <= '0';
        wait on IbCmd.Ack;
    end procedure sendnotlastcompletition;

    -----------------------------------------------------------------------
    -- Send Not Last Completition Transaction with Data from File (op_done is not generated)
    procedure sendnotlastcompletitionfile (
        constant dstaddr  : in std_logic_vector(31 downto 0); -- Destination addres of write transaction
        constant srcaddr  : in std_logic_vector(31 downto 0); -- From where are write transaction generated
        constant length   : in integer;                       -- Length of writen data
        constant tag      : in integer;                       -- Transaction Tag
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is

        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
    begin
        if (length = 0) then
            len := FileLineCount(filename)*8;
        else
            len := length;
        end if;
        assert (len <= MAX_TRANS_LENGTH)
            report "Transaction length exceed 4095 bytes IB limit"
            severity ERROR;
        IbCmdV.CmdOp       := Completition;
        IbCmdV.Di.SrcAddr  := srcaddr;
        IbCmdV.Di.DstAddr  := dstaddr;
        IbCmdV.Di.Length   := len;
        IbCmdV.Di.Tag      := tag;
        IbCmdV.Di.LastFlag := '0';
        file_open(in_file, filename, READ_MODE);
        i                  := 0;
        while (i < len) loop
            readline(in_file, in_line);
            hread(in_line, IbCmdV.Di.Data(i/8), readflag);
            assert readflag
                report "SendNotLastCompletitionFile read error"
                severity ERROR;
            i := i+8;
        end loop;
        file_close(in_file);

        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req <= '0';
        wait on IbCmd.Ack;
    end procedure sendnotlastcompletitionfile;

    -----------------------------------------------------------------------
    -- Enable Transcript Logging
    procedure settranscriptlogging (
        constant enable   : in boolean;                       -- Enable/Disable
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        IbCmdV.CmdOp       := TranscriptLogging;
        IbCmdV.Di.Enable   := enable;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req          <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req          <= '0';
        wait on IbCmd.Ack;
    end procedure settranscriptlogging;

    -----------------------------------------------------------------------
    -- Enable File Logging
    procedure setfilelogging (
        constant enable   : in boolean;                       -- Enable/Disable
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        IbCmdV.CmdOp       := FileLogging;
        IbCmdV.Di.Enable   := enable;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req          <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req          <= '0';
        wait on IbCmd.Ack;
    end procedure setfilelogging;

    -----------------------------------------------------------------------
    -- Init HostPC Memory
    procedure initmemory (
        constant length   : in integer;                       -- Length of writen data
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
    begin
        if (length = 0) then
            len := FileLineCount(filename)*8;
        else
            len := length;
        end if;
        assert (len <= MAX_INIT_DATA)
            report "Transaction length exceed 4096 bytes memory init limit"
            severity ERROR;
        IbCmdV.CmdOp      := InitMemory;
        IbCmdV.Di.Length  := length;
        IbCmdV.Di.MemAddr := 0;

        file_open(in_file, filename, READ_MODE);
        i := 0;
        while (i < len) loop
            readline(in_file, in_line);
            hread(in_line, IbCmdV.Di.Data(i/8), readflag);
            assert readflag
                report "InitMemory read error"
                severity ERROR;
            i := i+8;
        end loop;
        file_close(in_file);

        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req <= '0';
        wait on IbCmd.Ack;
    end procedure initmemory;

    -----------------------------------------------------------------------
    -- Init HostPC Memory Starting From Given Address
    procedure initmemoryfromaddr (
        constant length   : in integer;                       -- Length of writen data
        constant address  : in integer;                       -- Where to write data
        constant filename : in string;                        -- Filename from where are data writen (64 bit hexa values)
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
        file     in_file      : text;
        variable in_line      : line;
        variable readflag     : boolean;
        variable len          : integer;
        variable i            : integer;
    begin
        if (length = 0) then
            len := FileLineCount(filename)*8;
        else
            len := length;
        end if;
        assert (len <= MAX_INIT_DATA)
            report "Transaction length exceed 4096 bytes memory init limit"
            severity ERROR;
        IbCmdV.CmdOp      := InitMemoryFromAddr;
        IbCmdV.Di.Length  := length;
        IbCmdV.Di.MemAddr := address;

        file_open(in_file, filename, READ_MODE);
        i := 0;
        while (i < len) loop
            readline(in_file, in_line);
            hread(in_line, IbCmdV.Di.Data((i)/8), readflag);
            assert readflag
                report "InitMemoryFromAddr read error"
                severity ERROR;
            i := i+8;
        end loop;
        file_close(in_file);

        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req <= '0';
        wait on IbCmd.Ack;
    end procedure initmemoryfromaddr;

    -----------------------------------------------------------------------
    -- Show content of Memory
    procedure showmemory (
        signal   ibcmd    : inout IbCmdType                   -- Command record
    ) is
    begin
        IbCmdV.CmdOp := ShowMemory;
        -- Req toggles each time we want the BFM to do a new check.
        IbCmd.Req    <= '1';
        wait on IbCmd.ReqAck;
        IbCmd.Req    <= '0';
        wait on IbCmd.Ack;
    end procedure showmemory;
end package body;

