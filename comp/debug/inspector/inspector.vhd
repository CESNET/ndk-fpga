-- inspector.vhd: debugger and analyser
-- Copyright (C) 2016 CESNET
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use work.math_pack.all;
use work.inspector_pkg.all;

entity INSPECTOR is
generic (
   DEVICE                           : string  := "ULTRASCALE";
   ENABLE                           : boolean := true;
   IOBJ_COUNT                       : integer := 0;

   inspector_objects                : t_inspector_objects_int := (0 => IOBJ_RESET, 1 => IOBJ_STROBE, others => IOBJ_NONE);
   inspector_histogram_bucket_count : t_inspector_objects_int := (others => 0);
   inspector_object_group           : t_inspector_objects_int := (others => 0)
   );
port (
    --! \name CLOCK and RESET
   CLK                  : in std_logic;
   RESET                : in std_logic;

   INPUT                : in  t_inspector_inputs (IOBJ_COUNT-1 downto 0);
   OUTPUT               : out t_inspector_outputs(IOBJ_COUNT-1 downto 0);

   --! \name MI32 interface
   MI_DWR               : in  std_logic_vector(31 downto 0);
   MI_ADDR              : in  std_logic_vector(31 downto 0);
   MI_RD                : in  std_logic;
   MI_WR                : in  std_logic;
   MI_BE                : in  std_logic_vector(3 downto 0);
   MI_DRD               : out std_logic_vector(31 downto 0);
   MI_ARDY              : out std_logic := '0';
   MI_DRDY              : out std_logic := '0'
);
end entity;

architecture full of INSPECTOR is

   type t_object_mi_drd             is array(IOBJ_COUNT-1 downto 0) of std_logic_vector(31 downto 0);

   signal object_mi_drd             : t_object_mi_drd;
   signal reg_input                 : t_inspector_inputs(IOBJ_COUNT-1 downto 0);

   signal mi_object                 : std_logic_vector(IOBJ_COUNT-1 downto 0);
   signal group_reset               : std_logic_vector(31 downto 0);
   signal group_strobe              : std_logic_vector(31 downto 0);

begin

   reg_inputp : process(CLK)
   begin
      if(CLK'event and CLK = '1') then
         reg_input      <= INPUT;
      end if;
   end process;

   MI_ARDY     <= MI_RD or MI_WR;
   MI_DRDY     <= MI_RD;
   MI_DRD      <= object_mi_drd(conv_integer(MI_ADDR(log2(IOBJ_COUNT)+2 downto 3)));

   gen_enable: if (ENABLE) generate

   addrdec_p: process(MI_ADDR, MI_WR)
   begin
      mi_object <= (others => '0');
      for i in 0 to IOBJ_COUNT-1 loop
         if(i = MI_ADDR(log2(IOBJ_COUNT)+2 downto 3)) then
            mi_object(i) <= '1';
         end if;
      end loop;
   end process;

   inspector_objects_gen : for i in 0 to IOBJ_COUNT-1 generate

      gen_reset : if(inspector_objects(i) = IOBJ_RESET) generate
         reg_resetp : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(mi_object(i) = '1' and MI_WR = '1') then
                  group_reset <= MI_DWR;
               else
                  group_reset <= (others => '0');
               end if;
            end if;
         end process;
      end generate;

      gen_strobe : if(inspector_objects(i) = IOBJ_STROBE) generate
         reg_strobep : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(mi_object(i) = '1' and MI_WR = '1') then
                  group_strobe <= MI_DWR;
               else
                  group_strobe <= (others => '0');
               end if;
            end if;
         end process;
      end generate;

      gen_outputreg : if(inspector_objects(i) = IOBJ_OUTPUTREG) generate
         reg_outregp : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(mi_object(i) = '1' and MI_WR = '1') then
                  if(MI_ADDR(2) = '1') then
                     OUTPUT(i).outputreg(63 downto 32) <= MI_DWR;
                  else
                     OUTPUT(i).outputreg(31 downto  0) <= MI_DWR;
                  end if;
               end if;
            end if;
         end process;
      end generate;

      gen_inputreg : if(inspector_objects(i) = IOBJ_INPUTREG) generate
         signal inspector_inputreg_int   : std_logic_vector(63 downto 0);
      begin
         object_mi_drd(i)  <= inspector_inputreg_int(63 downto 32) when MI_ADDR(2) = '1' else
                              inspector_inputreg_int(31 downto  0);
         reg_outregp : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(reg_input(i).inputreg_we = '1') then
                  inspector_inputreg_int <= reg_input(i).inputreg;
               end if;
            end if;
         end process;
      end generate;

      gen_counter : if(inspector_objects(i) = IOBJ_COUNTER) generate
         signal inspector_counter_reg     : std_logic_vector(47 downto 0);
         signal inspector_counter_value   : std_logic_vector(47 downto 0);
         signal inspector_counter_add     : std_logic_vector(26 downto 0);
      begin

         object_mi_drd(i)  <= X"0000" &   inspector_counter_reg(47 downto 32) when MI_ADDR(2) = '1' else
                                          inspector_counter_reg(31 downto  0);

         inspector_counter_add <= conv_std_logic_vector(reg_input(i).counter_inc, 27);

         counter_i : entity work.DSP_COUNTER
         generic map(
            DEVICE       => DEVICE,
            INPUT_REGS   => true  ,
            INPUT_WIDTH  => 27    , -- Maximum supported value
            OUTPUT_WIDTH => 48    ,
            DSP_ENABLE   => true
         )
         port map(
            CLK       => CLK,
            CLK_EN    => reg_input(i).counter_ce,
            RESET     => group_reset(inspector_object_group(i)),
            INCREMENT => inspector_counter_add,
            MAX_VAL   => (others => '1'),
            RESULT    => inspector_counter_value
         );

         reg_strobep : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(group_strobe(inspector_object_group(i)) = '1') then
                  inspector_counter_reg   <= inspector_counter_value;
               end if;
            end if;
         end process;
      end generate;

      gen_histogram : if(inspector_objects(i) = IOBJ_HISTOGRAM) generate
         signal histogram_select : std_logic_vector(inspector_histogram_bucket_count(i)-1 downto 0);
         signal histogram_select_ce : std_logic_vector(inspector_histogram_bucket_count(i)-1 downto 0);
         signal histogram_select_mi : std_logic_vector(log2(inspector_histogram_bucket_count(i))-1 downto 0);

         type t_inspector_histogram_bucket_reg is array(inspector_histogram_bucket_count(i)-1 downto 0) of std_logic_vector(47 downto 0);
         signal histogram_bucket_reg : t_inspector_histogram_bucket_reg;
         signal histogram_bucket_value : t_inspector_histogram_bucket_reg;

      begin
         object_mi_drd(i)  <= X"0000" &   histogram_bucket_reg(conv_integer(histogram_select_mi))(47 downto 32) when MI_ADDR(2) = '1' else
                                          histogram_bucket_reg(conv_integer(histogram_select_mi))(31 downto  0);

         reg_bucketaddrp : process(CLK)
         begin
            if(CLK'event and CLK = '1') then
               if(mi_object(i) = '1' and MI_WR = '1') then
                  histogram_select_mi <= MI_DWR(log2(inspector_histogram_bucket_count(i))-1 downto 0);
               end if;
            end if;
         end process;

         gen_histogram_buckets : for j in 0 to inspector_histogram_bucket_count(i)-1 generate
            signal ce : std_logic;
         begin
            ce          <= '1' when reg_input(i).histogram_ce = '1' and reg_input(i).histogram_bucket = j else '0';

            counter_i : entity work.DSP_COUNTER
            generic map(
                DEVICE       => DEVICE,
                INPUT_REGS   => true  ,
                INPUT_WIDTH  => 1     ,
                OUTPUT_WIDTH => 48    ,
                DSP_ENABLE   => true
            )
            port map(
                CLK       => CLK,
                CLK_EN    => ce ,
                RESET     => group_reset(inspector_object_group(i)),
                INCREMENT => (others => '1'),
                MAX_VAL   => (others => '1'),
                RESULT    => histogram_bucket_value(j)
            );

            reg_histogramregp : process(CLK)
            begin
               if(CLK'event and CLK = '1') then
                  if(group_strobe(inspector_object_group(i)) = '1') then
                     histogram_bucket_reg(j) <= histogram_bucket_value(j);
                  end if;
               end if;
            end process;

         end generate;

      end generate;

   end generate;

   end generate;
end architecture;
