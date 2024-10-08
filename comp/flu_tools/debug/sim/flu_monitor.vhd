--
-- flu_monitor.vhd: FrameLinkUnaligned monitoring unit flu_logging based
-- subcomponent
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
use IEEE.std_logic_arith.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;
use work.flu_bfm_pkg.all;
use work.flu_bfm_rdy_pkg.all;
-- library containing log2 function
use work.math_pack.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity MONITOR is
   generic(
      -- FrameLink data bus width
      DATA_WIDTH        : integer;
      SOP_POS_WIDTH     : integer;
      FILE_NAME         : string;  -- Log File Path
      RDY_DRIVER        : RDYSignalDriver
   );
   port(
      -- Common interface
      FLU_RESET          : in  std_logic;
      FLU_CLK            : in  std_logic;

      -- RX Frame link Interface
      RX_DATA        : in std_logic_vector(DATA_WIDTH-1 downto 0);
      RX_SOP_POS     : in std_logic_vector(SOP_POS_WIDTH-1 downto 0);
      RX_EOP_POS     : in std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
      RX_SOP         : in std_logic;
      RX_EOP         : in std_logic;
      RX_SRC_RDY     : in std_logic;
      RX_DST_RDY     : out  std_logic
     );
end entity MONITOR;

architecture MONITOR_ARCH of MONITOR is

   -- start of packet and end of packet character
   constant dolar: character :='$';

   signal   data        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal   sop_pos     : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal   eop_pos     : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal   sop         : std_logic;
   signal   eop         : std_logic;
   signal   src_rdy     : std_logic;
   signal   dst_rdy     : std_logic;
   signal   dst_rdy_sig : std_logic;
   -- signal for extended sop_pos
   signal   ext_sop_pos : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);

begin
   -- sop_pos signal extansion
   ext_sop_pos  <= sop_pos & (log2(DATA_WIDTH/8)-SOP_POS_WIDTH-1 downto 0 => '0')
   when
      SOP_POS_WIDTH<log2(DATA_WIDTH/8)
   else
      sop_pos;

   -- Repeater
   data       <= RX_DATA;
   sop_pos    <= RX_SOP_POS;
   eop_pos    <= RX_EOP_POS;
   sop        <= RX_SOP;
   eop        <= RX_EOP;
   src_rdy    <= RX_SRC_RDY;
   RX_DST_RDY <= dst_rdy and dst_rdy_sig;

-- Logging process
main_process:process

-- variables
file output_file: TEXT;
variable file_status: file_open_status;
variable out_line   : line;
variable my_data : std_logic_vector(DATA_WIDTH-1 downto 0);
variable var_ext_sop_pos : integer := 2;
variable var_eop_pos : integer := 2;
variable j, i : integer;
variable space : integer := 0;
variable s_space : string(1 to 3);

begin
   dst_rdy_sig <= '0';
   wait until (FLU_RESET='0');
   dst_rdy_sig <= '1';
   -- Open output file for write
   assert (FILE_NAME/="") report "MONITOR: Empty file name!" severity failure;
   if (FILE_NAME/="") then
      file_open(file_status,output_file,FILE_NAME,write_mode);
      assert (file_status = OPEN_OK) report "MONITOR: File couldn't be created!" severity failure;
      if (file_status = OPEN_OK) then
         file_close(output_file);
         -- data will be written
         while (FLU_RESET='0') loop
            -- wait for clk = '1' and src_rdy = '1' and dst_rdy = '1'
            loop
               wait until (FLU_CLK'event and FLU_CLK='1');
               wait for 0.5 ps;
               if(src_rdy = '1' and dst_rdy = '1') then
                  exit;
               end if;
            end loop;
            file_open(output_file,FILE_NAME,append_mode);
            -- convert signals to integer and convert from bytes to bits(*8)
            var_ext_sop_pos := conv_integer(ext_sop_pos)*8;
            var_eop_pos     := conv_integer(eop_pos)*8;

            -- mirror data
            j := DATA_WIDTH/4;
            for i in 1 to DATA_WIDTH/4 loop
               my_data((j*4)-1 downto (j-1)*4) := data((i*4)-1 downto (i-1)*4);
               j := j-1;
            end loop;

            if (sop = '1' and eop = '1') then
               -- packet ends and starts new in one transaction
               if(var_ext_sop_pos > var_eop_pos) then
                  -- write only valid data of ended packet in hexa
                  hwrite(out_line, my_data(DATA_WIDTH-1 downto DATA_WIDTH-var_eop_pos-8));
                  writeline(output_file, out_line);

                  -- write dolar
                  write(out_line, dolar);
                  -- calculate space according to sop_pos and eop_pos
                  space := (var_ext_sop_pos/8) - (var_eop_pos/8) -1;
                  -- convert integer to string (function declared in flu_bfm_pkg.vhd)
                  s_space := int2str(space);
                  -- write space
                  write(out_line,s_space);
                  space := 0;
                  writeline(output_file, out_line);

                  -- write only valid data of start of packet in hexa
                  hwrite(out_line, my_data(DATA_WIDTH-1-var_ext_sop_pos downto 0));
               end if;
               -- one packet starts and ends in one transaction
               if (var_ext_sop_pos <= var_eop_pos) then
                  -- calculate space before packet and write dolar and space
                  space:= space + (var_ext_sop_pos/8);
                  write(out_line, dolar);
                  s_space := int2str(space);
                  write(out_line,s_space);
                  space := 0;
                  writeline(output_file, out_line);

                  -- calculate space after packet
                  space := space + (DATA_WIDTH/8) - (var_eop_pos/8) - 1;
                  -- write only valid data in hexa
                  hwrite(out_line, my_data(DATA_WIDTH-1-var_ext_sop_pos downto DATA_WIDTH-var_eop_pos-8));
                  writeline(output_file, out_line);
               end if;
            elsif (sop = '1') then
               -- calculate space before packet and write dolar and space
               space:= space + (var_ext_sop_pos/8);
               s_space := int2str(space);
               write(out_line, dolar);
               write(out_line,s_space);
               space := 0;
               writeline(output_file, out_line);

               -- write only valid data in hexa
               hwrite(out_line, my_data(DATA_WIDTH-1-var_ext_sop_pos downto 0));
            elsif (eop = '1') then
               -- write only valid data in hexa
               if out_line'length >= (DATA_WIDTH/4)-1 then
                  writeline(output_file, out_line);
               end if;
               hwrite(out_line, my_data(DATA_WIDTH-1 downto DATA_WIDTH-var_eop_pos-8));
               writeline(output_file, out_line);
               -- calculate space
               space := space + (DATA_WIDTH/8) - (var_eop_pos/8) - 1;
            else
               writeline(output_file, out_line);
               hwrite(out_line,my_data(DATA_WIDTH-1 downto 0));
            end if;
            file_close(output_file);
         end loop;
      end if;
   end if;
   dst_rdy_sig<='0';
end process;

DRIVE_DST_RDY_N: PROCESS
  BEGIN
    LOOP
      IF (RDY_DRIVER = EVER) then
         DriveRdyNAll(FLU_CLK, dst_rdy);
      elsif (RDY_DRIVER = ONOFF) then
         DriveRdyN50_50(FLU_CLK, dst_rdy);
      elsif (RDY_DRIVER = RND) then
         DriveRdyNRnd(FLU_CLK, dst_rdy);
      end if;
    END LOOP;
  END PROCESS;

end architecture MONITOR_ARCH;
