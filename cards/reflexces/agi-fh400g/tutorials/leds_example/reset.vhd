--!
--! reset.vhd: Reset synchronizer.
--! Copyright (C) 2014 CESNET
--! Author(s): Jakub Cabal <jakubcabal@gmail.com>
--!            Lukas Kekely <kekely@cesnet.cz>
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;

entity ASYNC_RESET is
   Generic (
      TWO_REG  : BOOLEAN := false; --! For two reg = true, for three reg = false
      OUT_REG  : BOOLEAN := false; --! Registering of output reset by single normal register in destination clock domain.
      REPLICAS : INTEGER := 1      --! Number of output register replicas (registers actually replicated only when OUT_REG is true).
   );    
   Port (
      --! A clock domain 
      CLK        : in  STD_LOGIC; --! Clock
      ASYNC_RST  : in  STD_LOGIC; --! Asynchronous reset
      OUT_RST    : out STD_LOGIC_VECTOR(max(REPLICAS,1)-1 downto 0) --! Output reset
   );
end ASYNC_RESET;

   --! -------------------------------------------------------------------------
   --!                      Architecture declaration
   --! -------------------------------------------------------------------------

architecture FULL of ASYNC_RESET is

   --! -------------------------------------------------------------------------
   --! Signals
   --! -------------------------------------------------------------------------
   
   signal rff1    : std_logic := '1';
   signal rff2    : std_logic := '1';
   signal rff_out : std_logic := '1';

   --! Xilinx attributes declarations
   attribute dont_touch            : string;
   attribute shreg_extract         : string;
   attribute async_reg             : string;
   
   --! Xilinx attributes for rff1_reg and rff2_reg
   -- attribute dont_touch of rff1    : signal is "true";
   attribute shreg_extract of rff1 : signal is "no";
   attribute async_reg of rff1     : signal is "true";

   attribute shreg_extract of rff2 : signal is "no";
   attribute async_reg of rff2     : signal is "true";

   --! Intel attributes
   attribute maxfan                   : integer;
   attribute ALTERA_ATTRIBUTE         : string;
   attribute ALTERA_ATTRIBUTE of rff1 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON; -name SYNCHRONIZER_IDENTIFICATION FORCED";
   attribute ALTERA_ATTRIBUTE of rff2 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";

   --! -------------------------------------------------------------------------
 
begin

   --! -------------------------------------------------------------------------

   --! Two synchronization registers
   rff1_sync_reg : process(CLK, ASYNC_RST)
   begin
      if (ASYNC_RST = '1') then
         rff1 <= '1';
      elsif (rising_edge(CLK)) then
         rff1 <= '0';
      end if;
   end process;

   rff2_sync_reg : process(CLK, ASYNC_RST)
   begin
      if (ASYNC_RST = '1') then
         rff2 <= '1';
      elsif (rising_edge(CLK)) then
         rff2 <= rff1;
      end if;
   end process;

   --! -------------------------------------------------------------------------
   
   --! Generics two synchronization registers
   two_reg_sync : if TWO_REG generate

      rff_out <= rff2;
  
   end generate;  
  
   --! -------------------------------------------------------------------------
  
   --! Generics three synchronization registers
   three_reg_sync : if NOT TWO_REG generate
      
      --! Signals
      signal rff3                     : std_logic := '1';
      
      --! Attributes for rff3_reg
      attribute shreg_extract of rff3    : signal is "no";
      attribute async_reg of rff3        : signal is "true";
      attribute ALTERA_ATTRIBUTE of rff3 : signal is "-name ADV_NETLIST_OPT_ALLOWED NEVER_ALLOW; -name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";
   
      begin
   
      rff3_reg : process(CLK, ASYNC_RST)
         begin
         if (ASYNC_RST = '1') then
            rff3 <= '1';
         elsif (rising_edge(CLK)) then
            rff3 <= rff2; 
         end if;
      end process;
 
      rff_out <= rff3;
 
   end generate;

   --! -------------------------------------------------------------------------

   --! Generics do not use output register
   no_out_reg_gen : if not OUT_REG or REPLICAS = 0 generate

      OUT_RST <= (others => rff_out);

   end generate;

   --! -------------------------------------------------------------------------

   --! Generics output registers usage
   out_reg_gen : if OUT_REG and REPLICAS > 0 generate

      replicas_gen : for i in 0 to REPLICAS-1 generate

         signal rff_reg_out                  : std_logic := '1';
         
         attribute dont_touch of rff_reg_out       : signal is "true";
         attribute maxfan of rff_reg_out           : signal is 64;
         attribute ALTERA_ATTRIBUTE of rff_reg_out : signal is "-name DONT_MERGE_REGISTER ON; -name PRESERVE_REGISTER ON";

         begin

         out_reg : process(CLK)
            begin
            if (rising_edge(CLK)) then
               rff_reg_out <= rff_out;
            end if;
         end process;

         OUT_RST(i) <= rff_reg_out;

      end generate;

   end generate;

   --! -------------------------------------------------------------------------

end architecture FULL;
