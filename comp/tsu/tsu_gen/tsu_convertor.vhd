--! tsu_convertor.vhd
--!
--! @file
--! \brief timestamp unit - format convertor
--! \author Jakub Cabal <jakubcabal@gmail.com>
--! \date 2014
--!
--! @section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity TSU_CONVERTOR is
   generic (
      --! \brief Selects smarter DSPs arrangement for timestamp format conversion
      --! \details Meanings of supported values: \n
      --! true = use multiplication in DSPs composed of adds and shifts \n
      --! false = look at TS_MULT_USE_DSP
      TS_MULT_SMART_DSP            : boolean := true;
      --! \brief Selects whether to use DSPs for timestamp format conversion
      --! \details Meanings of supported values: \n
      --! true = use multipliers in DSPs \n
      --! false = disable DSPs, use logic
      TS_MULT_USE_DSP              : boolean := true
   );
   port (
      CLK     : in  std_logic;
      RESET   : in  std_logic;
      TS      : in  std_logic_vector(63 downto 0);
      TS_NS   : out std_logic_vector(63 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of TSU_CONVERTOR is

   --! \name Signals used with DSP's enabled code block
   signal reg_input1              : std_logic_vector(31 downto 0);
   signal reg_input2              : std_logic_vector(31 downto 0);
   signal reg_input3              : std_logic_vector(31 downto 0);
   signal reg_output1             : std_logic_vector(31 downto 0);
   signal reg_output2             : std_logic_vector(31 downto 0);
   signal reg_output3             : std_logic_vector(31 downto 0);
   signal multt                   : std_logic_vector(63 downto 0);
   signal reg_upper_ts1           : std_logic_vector(31 downto 0);
   signal reg_upper_ts2           : std_logic_vector(31 downto 0);
   signal reg_upper_ts3           : std_logic_vector(31 downto 0);
   signal reg_upper_ts4           : std_logic_vector(31 downto 0);
   signal reg_upper_ts5           : std_logic_vector(31 downto 0);
   signal reg_upper_ts6           : std_logic_vector(31 downto 0);

   --! \name Signals used with DSP's disabled code block
   signal no_dsp_reg_input1         : std_logic_vector(31 downto 0);
   signal no_dsp_reg_input2         : std_logic_vector(31 downto 0);
   signal no_dsp_reg_output1        : std_logic_vector(29 downto 0);
   signal no_dsp_reg_output2        : std_logic_vector(29 downto 0);
   signal no_dsp_multt              : std_logic_vector(47 downto 0);
   signal no_dsp_shift_reg_input2_2 : std_logic_vector(34 downto 0);
   signal no_dsp_sum1               : std_logic_vector(34 downto 0);
   signal no_dsp_sum2               : std_logic_vector(43 downto 0);
   signal no_dsp_sum                : std_logic_vector(47 downto 0);
   signal no_dsp_reg_upper_ts1      : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts2      : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts3      : std_logic_vector(31 downto 0);
   signal no_dsp_reg_upper_ts4      : std_logic_vector(31 downto 0);

   --! \name Attributes used with DSP's disabled code block
   attribute use_dsp : string;
   attribute use_dsp of no_dsp_multt : signal is "no";

begin

-- ----------------------------------------------------------------------------
-- TIMESTAMP FORMAT CONVERT - FRACTIONAL TO NANOSECOND
-- ----------------------------------------------------------------------------

   dont_use_smart_dsp : if not TS_MULT_SMART_DSP generate
      --! generate code that uses DSP blocks for timestamp format conversion
      use_mult_dsp : if TS_MULT_USE_DSP = true generate
         --! Pipelined conversion of fractinal part of timestamp to ns format
         frac_part_to_ns : process(CLK)
         begin
            if (CLK'event and CLK = '1') then
               reg_input1 <= TS(31 downto 0);
               reg_input2 <= reg_input1;
               reg_input3 <= reg_input2;
               reg_output1 <= multt(63 downto 32);
               reg_output2 <= reg_output1;
               reg_output3 <= reg_output2;

               reg_upper_ts1 <= TS(63 downto 32);
               reg_upper_ts2 <= reg_upper_ts1;
               reg_upper_ts3 <= reg_upper_ts2;
               reg_upper_ts4 <= reg_upper_ts3;
               reg_upper_ts5 <= reg_upper_ts4;
               reg_upper_ts6 <= reg_upper_ts5;
            end if;
         end process;

         --! actual conversion of fractinal part of timestamp to ns format
         --! it is made by multiplying every lower part of timestamp (31 downto 0) by a constant X"3B9ACA00"
         multt <= reg_input3 * X"3B9ACA00";

         --! connection to ts_ns port
         TS_NS <= reg_upper_ts6 & reg_output3;
      end generate use_mult_dsp;

      --! generate code that uses just logic (no DSP's) for timestamp format conversion
      dont_use_mult_dsp : if TS_MULT_USE_DSP = false generate
         --! Pipelined conversion of fractinal part of timestamp to ns format
         frac_part_to_ns : process(CLK)
         begin
            if (CLK'event and CLK = '1') then
               no_dsp_reg_input1  <= TS(31 downto 0);
               no_dsp_reg_input2  <= no_dsp_reg_input1;
               no_dsp_reg_output1 <= no_dsp_sum(47 downto 18);
               no_dsp_reg_output2 <= no_dsp_reg_output1;

               no_dsp_reg_upper_ts1 <= TS(63 downto 32);
               no_dsp_reg_upper_ts2 <= no_dsp_reg_upper_ts1;
               no_dsp_reg_upper_ts3 <= no_dsp_reg_upper_ts2;
               no_dsp_reg_upper_ts4 <= no_dsp_reg_upper_ts3;
            end if;
         end process;

         --! actual conversion of fractinal part of timestamp to ns format
         --! it is made by multiplying every lower part of timestamp (31 downto 0) by a constant X"3B9ACA00"

         --! As problem with constrains doesn't allow us to use integrated DSP'S for multiplying we have to make
         --! it as a logic. Therefore there is some kind of optimalizations to make it more cheaper for sources usage:
         no_dsp_multt <= no_dsp_reg_input2 * "1110111001101011"; -- use just part of 3B9ACA00 constant (lower 14 bits are cutted off here)

         --! two bits of 14 that were cutted from 3B9ACA00 constant has value 1 => add particular value to incoming timestamp
         no_dsp_shift_reg_input2_2 <= "0" & no_dsp_reg_input2(31 downto 0) & "00"; -- multiply 4 - add first non-null bit
         no_dsp_sum1 <= no_dsp_reg_input2 + no_dsp_shift_reg_input2_2; -- add second non-null bit
         no_dsp_sum2 <= no_dsp_sum1 & "000000000";

         --! finally add counted value to multiplied part
         no_dsp_sum <= no_dsp_multt + no_dsp_sum1(34 downto 5);

         TS_NS <= no_dsp_reg_upper_ts4 & "00" & no_dsp_reg_output2;
      end generate dont_use_mult_dsp;
   end generate;

   --! Use multiplication composed of sums in DSPs
   use_smart_dsp : if TS_MULT_SMART_DSP generate
      --! Multiplication unit, 4 cycles latency
      dsp_mult_i : entity work.mult_1e9
      port map(
         clk   => CLK,
         din   => TS(31 downto 0),
         dout  => TS_NS(31 downto 0)
      );

      --! Pipelining upper half of timestamp, 4 cycles latency
      sec_part : process(CLK)
      begin
         if (CLK'event and CLK = '1') then
            reg_upper_ts1 <= TS(63 downto 32);
            reg_upper_ts2 <= reg_upper_ts1;
            reg_upper_ts3 <= reg_upper_ts2;
            reg_upper_ts4 <= reg_upper_ts3;
         end if;
      end process;
      TS_NS(63 downto 32) <= reg_upper_ts4;

   end generate;

-- ----------------------------------------------------------------------------
-- END OF TIMESTAMP CONVERT
-- ----------------------------------------------------------------------------

end architecture;
