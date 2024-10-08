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
use work.math_pack.all;
use work.ib_pkg.all;
use work.ib_sim_oper.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity IB_SIM is
   generic (
       UPSTREAM_LOG_FILE   : string :="";
       DOWNSTREAM_LOG_FILE : string :=""
       );
   port(
      -- Common interface
      IB_RESET          : in  std_logic;
      IB_CLK            : in  std_logic;

      -- Internal Bus Interface
      INTERNAL_BUS      : inout t_internal_bus64;

      -- IB SIM interface
      STATUS            : out t_ib_status;
      CTRL              : in  t_ib_ctrl;
      STROBE            : in  std_logic;
      BUSY              : out std_logic
      );
end entity IB_SIM;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_SIM_ARCH of IB_SIM is

  -- Signals
  signal port0_out_data        : std_logic_vector(63 downto 0);
  signal port0_out_sop         : std_logic;
  signal port0_out_sop_aux     : std_logic;
  signal port0_out_eop_aux     : std_logic;
  signal port0_out_eop         : std_logic;
  signal port0_out_src_rdy     : std_logic;
  signal port0_out_dst_rdy     : std_logic;

  signal ib_packet_fifo_re     : std_logic;
  signal ib_packet_fifo_we     : std_logic;
  signal ib_packet_data        : std_logic_vector(63 downto 0);
  signal ib_packet_sop         : std_logic;
  signal ib_packet_eop         : std_logic;
  signal ib_packet_fifo_full   : std_logic;
  signal ib_packet_fifo_empty  : std_logic;
  signal internal_bus_up       : t_internal_bus_link64;
  signal internal_bus_down     : t_internal_bus_link64;


        -- Input Interface
  signal write_align_data_in     : std_logic_vector(63 downto 0);
  signal write_align_data_in_vld : std_logic;
  signal write_align_eop         : std_logic;
  signal write_align_align_reg   : std_logic_vector(2 downto 0);
  signal write_align_init        : std_logic;
  signal write_align_length      : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
  signal write_align_dwr         : std_logic_vector(63 downto 0);
  signal write_align_be          : std_logic_vector(7 downto 0);
  signal write_align_wr          : std_logic;
  signal write_align_eop_wr      : std_logic;

begin

-- Upstream always ready
internal_bus_up.DST_RDY_N <= '0';

-- Loging Component Upstram --------------------------------------------------
IB_SIM_LOGING_UP : entity work.IB_SIM_LOGING
   generic map (
      FILE_NAME => UPSTREAM_LOG_FILE
      )
   port map (
      -- Common interface
      IB_CLK    => IB_CLK,
      IB_RESET  => IB_RESET,

      -- Repeater behaviour
      IB_IN     => INTERNAL_BUS.UP,
      IB_OUT    => internal_bus_up
      );

-- Loging Component Downstream -----------------------------------------------
IB_SIM_LOGING_DOWN : entity work.IB_SIM_LOGING
   generic map (
      FILE_NAME => DOWNSTREAM_LOG_FILE
      )
   port map (
      -- Common interface
      IB_CLK    => IB_CLK,
      IB_RESET  => IB_RESET,

      -- Repeater behaviour
      IB_IN     => internal_bus_down,
      IB_OUT    => INTERNAL_BUS.DOWN
      );

-- ----------------------------------------------------------------------------
WRITE_ALIGN_U : entity work.WRITE_ALIGN
   port map (
      -- Common Interface
      CLK            =>  IB_CLK,
      RESET          =>  IB_RESET,

      -- Input Interface
      DATA_IN        => write_align_data_in,
      DATA_IN_VLD    => write_align_data_in_vld,
      EOP            => write_align_eop,
      ALIGN_REG      => write_align_align_reg,
      ALIGN_INIT     => write_align_init,
      LENGTH         => write_align_length,
      --Output Interface
      DWR            => write_align_dwr,
      BE_WR          => write_align_be,
      WR             => write_align_wr,
      EOP_WR         => write_align_eop_wr
);

-- register port0_pipe ------------------------------------------------------
port0_pipep: process(IB_RESET, IB_CLK)
begin
   if (IB_RESET = '1') then
      internal_bus_down.DATA        <= X"0000000000000000";
      internal_bus_down.SOP_N       <= '1';
      internal_bus_down.EOP_N       <= '1';
      internal_bus_down.SRC_RDY_N   <= '1';
   elsif (IB_CLK'event AND IB_CLK = '1') then
     if (internal_bus_down.DST_RDY_N = '0') then
       internal_bus_down.DATA       <= port0_out_data;
       internal_bus_down.SOP_N      <= port0_out_sop_aux;
       internal_bus_down.EOP_N      <= port0_out_eop_aux;
       internal_bus_down.SRC_RDY_N  <= port0_out_src_rdy;
     end if;
   end if;
end process;

-- SOP on 1 when no data rdy
port0_out_sop_aux <= '1' when ib_packet_fifo_empty = '1' else port0_out_sop;
port0_out_eop_aux <= '1' when ib_packet_fifo_empty = '1' else port0_out_eop;

-- Read when dst_rdy
ib_packet_fifo_re <= not internal_bus_down.DST_RDY_N;

-- Source ready when data and dst_rdy
port0_out_src_rdy <= '0' when (ib_packet_fifo_empty = '0' and
                               internal_bus_down.DST_RDY_N = '0') else '1';
-- ----------------------------------------------------------------------------
ib_packet_fifo: entity work.fifo
   generic map (
    ITEMS => 1024,
    DATA_WIDTH => 66
   )
   port map(
      CLK       => IB_CLK,
      RESET     => IB_RESET,
      -- Write interface
      WRITE_REQ             => ib_packet_fifo_we,
      DATA_IN(63 downto 0)  => ib_packet_data,
      DATA_IN(64)           => ib_packet_sop,
      DATA_IN(65)           => ib_packet_eop,
      FULL                  => ib_packet_fifo_full,
      LSTBLK                => open,

      -- Read interface
      READ_REQ              => ib_packet_fifo_re,
      DATA_OUT(63 downto 0) => port0_out_data,
      DATA_OUT(64)          => port0_out_sop,
      DATA_OUT(65)          => port0_out_eop,
      EMPTY                 => ib_packet_fifo_empty
      );


main : process
-- ----------------------------------------------------------------
--                        Process Body
-- ----------------------------------------------------------------
variable src_addr     : std_logic_vector(31 downto 0);
variable dst_addr     : std_logic_vector(31 downto 0);
variable length       : std_logic_vector(11 downto 0);
variable trans_type   : std_logic_vector( 2 downto 0);
variable trans_flag   : std_logic;
variable tag          : std_logic_vector(15 downto 0);
variable data         : std_logic_vector(63 downto 0);
variable data32_1     : std_logic_vector(31 downto 0);
variable data32_2     : std_logic_vector(31 downto 0);
variable file_name    : t_file_name;
file     in_file      : text;
file     out_file     : text;
variable in_line      : line;
variable out_line     : line;
variable readFlag     : boolean;
variable items2write  : integer;
variable data2        : std_logic_vector(63 downto 0);
variable line_count   : integer;

begin

STATUS.DO <= (others => '0');
STATUS.DV <= '0';
BUSY      <= '0';

-- Set Default values for align circuit
write_align_data_in     <= (others => '0');
write_align_data_in_vld <= '0';
write_align_eop         <= '0';
write_align_align_reg   <= (others => '0');
write_align_length      <= (others => '0');
write_align_init        <= '0';


-- Wait when reset
wait until (IB_RESET = '0');

-- Do main loop
while true loop
  BUSY <= '0';
  wait until (STROBE = '1');
  BUSY <= '1';

  -- Get Data for creating packet
  src_addr     := CTRL.PARAMS.SRC_ADDR;
  dst_addr     := CTRL.PARAMS.DST_ADDR;
  length       := conv_std_logic_vector(CTRL.PARAMS.LENGTH, 12);
  tag          := conv_std_logic_vector(CTRL.PARAMS.TAG, 16);
  data         := CTRL.PARAMS.DATA;
  file_name    := CTRL.PARAMS.FILE_NAME;
  trans_flag   := CTRL.PARAMS.TRANS_FLAG;

  assert CTRL.PARAMS.LENGTH < 4096 report "Length must be 0, 4095" severity ERROR;

-- LOCAL READ -----------------------------------------------------
  if (CTRL.OPER = LOCAL_READ or CTRL.OPER = LOCAL_READ_FILE) then

    -- Open write file
    if (CTRL.OPER = LOCAL_READ_FILE) then
      file_open(out_file, file_name.arr(1 to file_name.len), WRITE_MODE);
    end if;

    -- Generate local read transaction
    ib_packet_data    <= src_addr & tag & trans_flag & C_IB_L2LR_TRANSACTION & length;
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & dst_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '0';
    ib_packet_fifo_we <= '1';
    if (not CTRL.READ_WAIT) then
      BUSY <= '0';
    end if;
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');


    if (CTRL.READ_WAIT) then
       ib_packet_fifo_we <= '0';
       wait until (internal_bus_up.SOP_N = '0' and IB_CLK'event and IB_CLK='1' and
                   internal_bus_up.SRC_RDY_N = '0' and internal_bus_up.DST_RDY_N = '0' and
                   internal_bus_up.DATA(31 downto 16) = tag);

       while (not (internal_bus_up.EOP_N = '0' and internal_bus_up.SRC_RDY_N = '0' and internal_bus_up.DST_RDY_N ='0')) loop
          wait until IB_CLK'event and IB_CLK='1';
          if internal_bus_up.SRC_RDY_N = '0' and internal_bus_up.DST_RDY_N = '0' then
             STATUS.DV <= '1';
             STATUS.DO <= internal_bus_up.DATA;
             if (CTRL.OPER = LOCAL_READ_FILE) then
               hwrite(out_line, internal_bus_up.DATA);
               writeline(out_file, out_line);
             end if;
          else
             STATUS.DO <= (others => '0');
             STATUS.DV <= '0';
          end if;
          end loop;

          -- Close File
          if (CTRL.OPER = LOCAL_READ_FILE) then
            file_close(out_file);
          end if;
          wait until IB_CLK'event and IB_CLK='1';
          BUSY <= '0';
          STATUS.DV <= '0';
    end if;

-- LOCAL WRITE -----------------------------------------------------
  elsif (CTRL.OPER = LOCAL_WRITE) then
    -- Init Write Align Circuit
    write_align_align_reg <= dst_addr(2 downto 0);
    write_align_length    <= length;
    write_align_init      <= '1';
    -- Generate local write transaction (64 bit word)
    ib_packet_data    <= dst_addr & tag & trans_flag & C_IB_L2LW_TRANSACTION & length;
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & src_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');

    -- Write 64 bit data to align circuit
    write_align_init        <= '0';
    write_align_data_in     <= data;
    write_align_data_in_vld <= '1';
    write_align_eop         <= '1';
    wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
    -- Write data from align circuit into fifo
    ib_packet_data    <= write_align_dwr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= not write_align_eop_wr;
    ib_packet_fifo_we <= write_align_wr;
    wait until (IB_CLK'event and IB_CLK='1');

    -- No other data will be writen
    write_align_data_in     <= (others => '0');
    write_align_data_in_vld <= '0';
    BUSY <= '0';
    wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
    if (write_align_wr = '1') then -- If last item is writen
      ib_packet_fifo_we <= write_align_wr;
      ib_packet_data    <= write_align_dwr;
      ib_packet_eop     <= not write_align_eop_wr;
      wait until (IB_CLK'event and IB_CLK='1');
    end if;


-- LOCAL WRITE FILE ------------------------------------------------
  elsif (CTRL.OPER = LOCAL_WRITE_FILE) then

    -- Generate local write transaction using file
    line_count:= file_line_count(file_name.arr(1 to file_name.len));
    file_open(in_file, file_name.arr(1 to file_name.len), READ_MODE);

    if (CTRL.PARAMS.LENGTH = 0) then
       items2write:= line_count;
       length:= conv_std_logic_vector(line_count*8, 12);
    else
       -- Items 2 Write
       if (CTRL.PARAMS.LENGTH mod 8) = 0 then
         items2write := CTRL.PARAMS.LENGTH/8;
       else
         items2write := CTRL.PARAMS.LENGTH/8+1;
       end if;
    end if;

    -- Init Write Align Circuit
    write_align_align_reg <= dst_addr(2 downto 0);
    write_align_length    <= length;
    write_align_init      <= '1';
    -- Generate local write transaction (64 bit word)
    ib_packet_data    <= dst_addr & tag & trans_flag & C_IB_L2LW_TRANSACTION & length;
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & src_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');

    while (items2write > 0) loop
      readline(in_file, in_line);
      hread(in_line, data, readFlag);
      assert readFlag report "ib_local_write_file FILE read error" severity ERROR;

       -- Write 64 bit data to align circuit
       write_align_init        <= '0';
       write_align_data_in     <= data;
       write_align_data_in_vld <= '1';
       if (items2write = 1) then
         write_align_eop         <= '1';
       else
         write_align_eop         <= '0';
       end if;
       wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
       ib_packet_data    <= write_align_dwr;
       ib_packet_sop     <= '1';
       ib_packet_eop     <= not write_align_eop_wr;
       ib_packet_fifo_we <= write_align_wr;
       wait until (IB_CLK'event and IB_CLK='1');
       items2write:=items2write-1;
    end loop;

    -- No other data will be writen
    write_align_data_in     <= (others => '0');
    write_align_data_in_vld <= '0';
    BUSY <= '0';
    wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
    if (write_align_wr = '1') then -- If last item is writen
      ib_packet_fifo_we <= write_align_wr;
      ib_packet_data    <= write_align_dwr;
      ib_packet_eop     <= not write_align_eop_wr;
      wait until (IB_CLK'event and IB_CLK='1');
    end if;

    file_close(in_file);




-- LOCAL WRITE FILE32 ----------------------------------------------
  elsif (CTRL.OPER = LOCAL_WRITE_FILE32) then

    -- Generate local write transaction using file
    line_count:= file_line_count(file_name.arr(1 to file_name.len));
    file_open(in_file, file_name.arr(1 to file_name.len), READ_MODE);

    if (CTRL.PARAMS.LENGTH = 0) then
       items2write:= (line_count / 2) + (line_count mod 2);
       length:= conv_std_logic_vector(line_count*4, 12);
    else
       -- Items 2 Write
       if (CTRL.PARAMS.LENGTH mod 8) = 0 then
         items2write := CTRL.PARAMS.LENGTH/8;
       else
         items2write := CTRL.PARAMS.LENGTH/8+1;
       end if;
    end if;

    -- Init Write Align Circuit
    write_align_align_reg <= dst_addr(2 downto 0);
    write_align_length    <= length;
    write_align_init      <= '1';
    -- Generate local write transaction (64 bit word)
    ib_packet_data    <= dst_addr & tag & trans_flag & C_IB_L2LW_TRANSACTION & length;
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & src_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');

    while (items2write > 0) loop
      readline(in_file, in_line);
      hread(in_line, data32_1, readFlag);
      assert readFlag report "ib_local_write_file32 FILE1 read error" severity ERROR;
      if (not endfile(in_file)) then
         readline(in_file, in_line);
         hread(in_line, data32_2, readFlag);
         assert readFlag report "ib_local_write_file32 FILE2 read error" severity ERROR;
      else
         data32_2:=X"00000000";
      end if;

       -- Write 64 bit data to align circuit
       write_align_init        <= '0';
       write_align_data_in     <= data32_2 & data32_1;
       write_align_data_in_vld <= '1';
       if (items2write = 1) then
         write_align_eop         <= '1';
       else
         write_align_eop         <= '0';
       end if;
       wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
       ib_packet_data    <= write_align_dwr;
       ib_packet_sop     <= '1';
       ib_packet_eop     <= not write_align_eop_wr;
       ib_packet_fifo_we <= write_align_wr;
       wait until (IB_CLK'event and IB_CLK='1');
       items2write:=items2write-1;
    end loop;

    -- No other data will be writen
    write_align_data_in     <= (others => '0');
    write_align_data_in_vld <= '0';
    BUSY <= '0';
    wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
    if (write_align_wr = '1') then -- If last item is writen
      ib_packet_fifo_we <= write_align_wr;
      ib_packet_data    <= write_align_dwr;
      ib_packet_eop     <= not write_align_eop_wr;
      wait until (IB_CLK'event and IB_CLK='1');
    end if;

    file_close(in_file);





 -- READ COMPLETITION ------------------------------------------------
  elsif (CTRL.OPER = READ_COMPLETITION) then

    -- Generate local write transaction using file
    line_count:= file_line_count(file_name.arr(1 to file_name.len));
    file_open(in_file, file_name.arr(1 to file_name.len), READ_MODE);

    if (CTRL.PARAMS.LENGTH = 0) then
       items2write:= line_count;
       length:= conv_std_logic_vector(line_count*8, 12);
    else
       -- Items 2 Write
       if (CTRL.PARAMS.LENGTH mod 8) = 0 then
         items2write := CTRL.PARAMS.LENGTH/8;
       else
         items2write := CTRL.PARAMS.LENGTH/8+1;
       end if;
    end if;

    -- Init Write Align Circuit
    write_align_align_reg <= dst_addr(2 downto 0);
    write_align_length    <= length;
    write_align_init      <= '1';
    -- Generate completition transaction (64 bit word)
    ib_packet_data    <= dst_addr & tag & trans_flag & C_IB_RD_COMPL_TRANSACTION & length; -- trans_flag - Last fragment
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & src_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');

    while (items2write > 0) loop
      readline(in_file, in_line);
      hread(in_line, data, readFlag);
      assert readFlag report "ib_local_write_file FILE read error" severity ERROR;

       -- Write 64 bit data to align circuit
       write_align_init        <= '0';
       write_align_data_in     <= data;
       write_align_data_in_vld <= '1';
       if (items2write = 1) then
         write_align_eop         <= '1';
       else
         write_align_eop         <= '0';
       end if;
       wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
       ib_packet_data    <= write_align_dwr;
       ib_packet_sop     <= '1';
       ib_packet_eop     <= not write_align_eop_wr;
       ib_packet_fifo_we <= write_align_wr;
       wait until (IB_CLK'event and IB_CLK='1');
       items2write:=items2write-1;
    end loop;

    -- No other data will be writen
    write_align_data_in     <= (others => '0');
    write_align_data_in_vld <= '0';
    BUSY <= '0';
    wait for 1 ns; -- Wait for write_align_dwr (Modelsim HACK)
    if (write_align_wr = '1') then -- If last item is writen
      ib_packet_fifo_we <= write_align_wr;
      ib_packet_data    <= write_align_dwr;
      ib_packet_eop     <= not write_align_eop_wr;
      wait until (IB_CLK'event and IB_CLK='1');
    end if;
    file_close(in_file);


 -- WRITE COMPLETITION ------------------------------------------------
  elsif (CTRL.OPER = WRITE_COMPLETITION) then
    -- Generate completition transaction (64 bit word)
    ib_packet_data    <= dst_addr & tag & '1' & C_IB_WR_COMPL_TRANSACTION & length;
    ib_packet_sop     <= '0';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '1';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
    ib_packet_data    <= X"00000000" & src_addr;
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '0';
    ib_packet_fifo_we <= '1';
    BUSY <= '0';
    wait until (ib_packet_fifo_full = '0' and IB_CLK'event and IB_CLK='1');
  end if;




    ib_packet_data    <= X"0000000000000000";
    ib_packet_sop     <= '1';
    ib_packet_eop     <= '1';
    ib_packet_fifo_we <= '0';
end loop;


end process;

end architecture IB_SIM_ARCH;

