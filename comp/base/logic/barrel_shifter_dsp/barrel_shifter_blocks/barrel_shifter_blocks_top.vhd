-- barrel_shifter_blocks_top.vhd: architecture of barrel shifter with DSP
-- Copyright (C) 2015 CESNET
-- Author(s): Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture shift_arch of BARREL_SHIFTER_BLOCKS is
   signal tmp_num_reg       : std_logic_vector(log2(MAX_SHIFT) - 1 downto 0);
   signal tmp_exp_reg       : std_logic_vector(MAX_SHIFT - 1 downto 0);
begin

   -- generate input registers
   GEN_SHIFT_EXP: if(SEL_FORMAT_SHIFT = 0) generate
      GEN_IN_REGS_NUM_SHIFT: if(REG_IN = 1) generate
         -- with DSP
         GEN_IN_REG_DSP: if(REGS_WITH_DSP = true) generate
            PIPE_inst: entity work.ALU_DSP
            generic map (
               DATA_WIDTH  => MAX_SHIFT,
               REG_IN      => 1,
               REG_OUT     => 0
            )
            port map (
               CLK         => CLK,
               RESET       => RESET,
               A           => SHIFT_EXP,
               B           => (others => '0'),
               CE_IN       => CE_IN,
               CE_OUT      => '1',
               ALUMODE     => "0000",
               CARRY_IN    => '0',
               P           => tmp_exp_reg
            );
         end generate;

         -- normal logic
         GEN_IN_REG_NORMAL: if(REGS_WITH_DSP = false) generate
            process(CLK)
            begin
               if (CLK'event) and (CLK = '1') then
                  if (RESET = '1') then
                     tmp_exp_reg <= (others => '0');
                  elsif (CE_OUT = '1') then
                     tmp_exp_reg <= SHIFT_EXP;
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      GEN_IN_REGS_NUM_SHIFT_OFF: if(REG_IN = 0) generate
         tmp_exp_reg <= SHIFT_EXP;
      end generate;
   end generate;

   GEN_SHIFT_BINARY: if(SEL_FORMAT_SHIFT = 1) generate
      GEN_IN_REGS_NUM_SHIFT: if(REG_IN = 1) generate
         -- with DSP
         GEN_IN_REG_DSP: if(REGS_WITH_DSP = true) generate
            PIPE_inst: entity work.ALU_DSP
            generic map (
               DATA_WIDTH  => log2(MAX_SHIFT),
               REG_IN      => 1,
               REG_OUT     => 0
            )
            port map (
               CLK         => CLK,
               RESET       => RESET,
               A           => SHIFT_BINARY,
               B           => (others => '0'),
               CE_IN       => CE_IN,
               CE_OUT      => '1',
               ALUMODE     => "0000",
               CARRY_IN    => '0',
               P           => tmp_num_reg
            );
         end generate;

         -- normal logic
         GEN_IN_REG_NORMAL: if(REGS_WITH_DSP = false) generate
            process(CLK)
            begin
               if (CLK'event) and (CLK = '1') then
                  if (RESET = '1') then
                     tmp_num_reg <= (others => '0');
                  elsif (CE_OUT = '1') then
                     tmp_num_reg <= SHIFT_BINARY;
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      GEN_IN_REGS_NUM_SHIFT_OFF: if(REG_IN = 0) generate
         tmp_num_reg <= SHIFT_BINARY;
      end generate;

      TO2N_inst: entity work.TO2N
            generic map (
               MAX_NUM     => MAX_SHIFT
            )
            port map (
               DATA_IN     => tmp_num_reg,
               DATA_OUT    => tmp_exp_reg
            );
   end generate;

   -- generate shifters
   GEN_SHIFTERS: for I in 0 to BLOCK_SIZE - 1 generate
      type tmp_inout_t is array (0 to BLOCK_SIZE) of std_logic_vector(BLOCKS - 1 downto 0);

      signal tmp_input  : tmp_inout_t;
      signal tmp_output : tmp_inout_t;
   begin

      GEN_INTER: for Y in 0 to BLOCKS - 1 generate
         tmp_input(I)(Y) <= DATA_IN(I + (Y * BLOCK_SIZE));
         DATA_OUT(I + (Y * BLOCK_SIZE)) <= tmp_output(I)(Y);
      end generate;

      GEN_ROTATE: if(EN_ROTATE = 1) generate
         GEN_SHIFTER_inst : entity work.BARREL_SHIFTER_DSP(rotate_arch)
            generic map (
               DATA_WIDTH => BLOCKS,
               SHIFT_LEFT => SHIFT_LEFT,
               REG_IN   => REG_IN,
               REG_OUT  => REG_OUT,
               REGS_WITH_DSP => REGS_WITH_DSP,
               MAX_SHIFT => MAX_SHIFT,
               SEL_FORMAT_SHIFT => 0
            )
            port map (
               CLK            => CLK,
               RESET          => RESET,
               DATA_IN        => tmp_input(I),
               DATA_OUT       => tmp_output(I),
               SHIFT_EXP      => tmp_exp_reg,
               SHIFT_BINARY   => (others => '0'),
               CE_IN          => CE_IN,
               CE_OUT         => CE_OUT
            );
      end generate;

      GEN_ROTATE_OFF: if(EN_ROTATE = 0) generate
         GEN_SHIFTER_inst : entity work.BARREL_SHIFTER_DSP(shift_arch)
            generic map (
               DATA_WIDTH => BLOCKS,
               SHIFT_LEFT => SHIFT_LEFT,
               REG_IN   => REG_IN,
               REG_OUT  => REG_OUT,
               REGS_WITH_DSP => REGS_WITH_DSP,
               MAX_SHIFT => MAX_SHIFT,
               SEL_FORMAT_SHIFT => 0
            )
            port map (
               CLK            => CLK,
               RESET          => RESET,
               DATA_IN        => tmp_input(I),
               DATA_OUT       => tmp_output(I),
               SHIFT_EXP      => tmp_exp_reg,
               SHIFT_BINARY   => (others => '0'),
               CE_IN          => CE_IN,
               CE_OUT         => CE_OUT
            );
      end generate;

   end generate;
end shift_arch;
