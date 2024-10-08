--! pipe_arch.vhd
--!
--! \file
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;

architecture full of PIPE_DSP is
   type tmp_t is array (0 to NUM_REGS) of std_logic_vector(DATA_WIDTH - 1  downto 0);
   signal tmp_inout  : tmp_t;
begin

   PIPE_TRUE: if(PIPE_EN = true and NUM_REGS /= 0) generate
      tmp_inout(0) <= DATA_IN;

      --! generate normal registers
      GEN_NORMAL_REGS: if(ENABLE_DSP = false) generate
         DATA_OUT     <= tmp_inout(NUM_REGS);

         GEN_REGS: for I in 0 to NUM_REGS - 1 generate
            process(CLK)
            begin
               if (CLK'event) and (CLK='1') then
                  if (RESET='1') then
                     tmp_inout(I + 1) <= (others => '0');
                  elsif (CE = '1') then
                     tmp_inout(I + 1) <= tmp_inout(I);
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      --! generate registers with DSPs
      GEN_DSP_REGS: if(ENABLE_DSP = true) generate
         GEN_DSPS: for I in 0 to (NUM_REGS/3)-1 generate
            DSP_PIPE_3x_inst: entity work.DSP_PIPE_3x
            generic map(
               DATA_WIDTH => DATA_WIDTH,
               NUM_REGS => 3
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DATA_IN => tmp_inout(I),
               DATA_OUT => tmp_inout(I + 1),
               CE => CE
            );
         end generate;

         GEN_DSP_MOD: if((NUM_REGS mod 3) /= 0) generate
            constant tmp : integer := NUM_REGS mod 3;
         begin
            DSP_PIPE_3x_inst: entity work.DSP_PIPE_3x
            generic map(
               DATA_WIDTH => DATA_WIDTH,
               NUM_REGS => tmp
            )
            port map (
               CLK => CLK,
               RESET => RESET,
               DATA_IN => tmp_inout((NUM_REGS/3)),
               DATA_OUT => tmp_inout((NUM_REGS/3)+1),
               CE => CE
            );

            DATA_OUT <= tmp_inout((NUM_REGS/3)+1);
         end generate;

         GEN_DSP_MOD_NO: if((NUM_REGS mod 3) = 0) generate
            DATA_OUT <= tmp_inout((NUM_REGS/3));
         end generate;
      end generate;
   end generate;

   PIPE_FALSE: if(PIPE_EN = false or NUM_REGS = 0) generate
      DATA_OUT <= DATA_IN;
   end generate;
end architecture;
