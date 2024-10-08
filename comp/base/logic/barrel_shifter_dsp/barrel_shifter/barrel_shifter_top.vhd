-- barrel_shifter_top.vhd: architecture of barrel shifter with DSP
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

architecture shift_arch of BARREL_SHIFTER_DSP is
   signal zeros : std_logic_vector(63 downto 0);

   constant MAX_SHIFT_D : integer := MAX_SHIFT / 16;
   constant MAX_SHIFT_M : integer := MAX_SHIFT mod 16;
   constant MAX_SHIFT_1 : integer := (MAX_SHIFT / 16) - 1;

   type tmp_out_t is array (0 to MAX_SHIFT_D) of std_logic_vector(DATA_WIDTH - 1 downto 0);
   signal tmp_out       : tmp_out_t;

   type tmp_shift_t is array (0 to MAX_SHIFT_D) of std_logic_vector(15 downto 0);
   signal tmp_shift     : tmp_shift_t;

   type tmp_cmp_t is array (0 to MAX_SHIFT_D) of std_logic_vector(1 downto 0);
   signal tmp_cmp       : tmp_cmp_t;

   signal data_out_reg        : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal num_shift_reg       : std_logic_vector(MAX_SHIFT-1 downto 0);
   signal shift_number_reg    : std_logic_vector(log2(MAX_SHIFT)-1 downto 0);

begin
   zeros <= (others => '0');

   -- generate output registers
   GEN_OUTPUT_REGISTERS: if(REG_OUT = 1 and MAX_SHIFT >= 16) generate
      -- with DSP
      GEN_OUT_REG_DSP: if(REGS_WITH_DSP = true) generate
         PIPE_inst: entity work.ALU_DSP
         generic map (
            DATA_WIDTH  => DATA_WIDTH,
            REG_IN      => 1,
            REG_OUT     => 0
         )
         port map (
            CLK         => CLK,
            RESET       => RESET,
            A           => data_out_reg,
            B           => (others => '0'),
            CE_IN       => CE_OUT,
            CE_OUT      => '1',
            ALUMODE     => "0000",
            CARRY_IN    => '0',
            P           => DATA_OUT
         );
      end generate;

      -- normal logic
      GEN_OUT_REG_NORMAL: if(REGS_WITH_DSP = false) generate
         process(CLK)
         begin
            if (CLK'event) and (CLK = '1') then
               if (RESET = '1') then
                     DATA_OUT <= (others => '0');
               elsif (CE_OUT = '1') then
                     DATA_OUT <= data_out_reg;
               end if;
            end if;
         end process;
      end generate;
   end generate;

   GEN_OUTPUT_REGISTERS_OFF: if(REG_OUT = 0 and MAX_SHIFT >= 16) generate
      DATA_OUT <= data_out_reg;
   end generate;

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
               P           => num_shift_reg
            );
         end generate;

         -- normal logic
         GEN_IN_REG_NORMAL: if(REGS_WITH_DSP = false) generate
            process(CLK)
            begin
               if (CLK'event) and (CLK = '1') then
                  if (RESET = '1') then
                     num_shift_reg <= (others => '0');
                  elsif (CE_OUT = '1') then
                     num_shift_reg <= SHIFT_EXP;
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      GEN_IN_REGS_NUM_SHIFT_OFF: if(REG_IN = 0) generate
         num_shift_reg <= SHIFT_EXP;
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
               P           => shift_number_reg
            );
         end generate;

         -- normal logic
         GEN_IN_REG_NORMAL: if(REGS_WITH_DSP = false) generate
            process(CLK)
            begin
               if (CLK'event) and (CLK = '1') then
                  if (RESET = '1') then
                     shift_number_reg <= (others => '0');
                  elsif (CE_OUT = '1') then
                     shift_number_reg <= SHIFT_BINARY;
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      GEN_IN_REGS_NUM_SHIFT_OFF: if(REG_IN = 0) generate
         shift_number_reg <= SHIFT_BINARY;
      end generate;

      -- convert format
      TO2N_inst: entity work.TO2N
            generic map (
               MAX_NUM     => MAX_SHIFT
            )
            port map (
               DATA_IN     => shift_number_reg,
               DATA_OUT    => num_shift_reg
            );
   end generate;

   -- generate dsp shifters
   GEN_DSP_SHIFTERS: for I in 0 to MAX_SHIFT_1 generate
   begin
      -- generate first shifter
      GEN_FIRST: if(I = 0) generate
         GEN_DSP_SHIFTER_inst: entity work.GEN_DSP_SHIFTER(full)
         generic map (
            DATA_WIDTH => DATA_WIDTH,
            SHIFT_LEFT => SHIFT_LEFT,
            REG_IN   => REG_IN,
            REG_OUT  => 0,
            REG_OUT_WITH_DSP => REGS_WITH_DSP
         )
         port map (
            CLK         => CLK,
            RESET       => RESET,
            DATA_IN     => DATA_IN,
            DATA_OUT    => tmp_out(I),
            NUM_SHIFT   => tmp_shift(I),
            CE_IN       => CE_IN,
            CE_OUT      => '1'
         );
      end generate;

      -- generate others shifters
      GEN_OTHERS: if(I /= 0) generate
         signal tmp_left_in : std_logic_vector(DATA_WIDTH - (I * 16) - 1 downto 0);
         signal tmp_left_out : std_logic_vector(DATA_WIDTH - (I * 16) - 1 downto 0);
      begin

         -- connect signals for left shift
         GEN_LEFT: if(SHIFT_LEFT = true) generate
            tmp_left_in <= tmp_out(I - 1)(DATA_WIDTH - 1 downto I * 16);
            tmp_out(I)((I * 16) - 1 downto 0) <= tmp_out(I - 1)((I * 16) - 1 downto 0);
            tmp_out(I)(DATA_WIDTH - 1 downto I * 16) <= tmp_left_out;
         end generate;

         -- connect signals for right shift
         GEN_RIGHT: if(SHIFT_LEFT = false) generate
            tmp_left_in <= tmp_out(I - 1)(DATA_WIDTH - (I * 16) - 1 downto 0);
            tmp_out(I)(DATA_WIDTH - 1 downto DATA_WIDTH - (I * 16)) <= tmp_out(I - 1)(DATA_WIDTH - 1 downto DATA_WIDTH - (I * 16));
            tmp_out(I)(DATA_WIDTH - (I * 16) - 1 downto 0) <= tmp_left_out;
         end generate;

         -- dsp shifter
         GEN_DSP_SHIFTER_inst: entity work.GEN_DSP_SHIFTER(full)
         generic map (
            DATA_WIDTH => DATA_WIDTH - (I * 16),
            SHIFT_LEFT => SHIFT_LEFT,
            REG_IN   => 0,
            REG_OUT  => 0
         )
         port map (
            CLK         => CLK,
            RESET       => RESET,
            DATA_IN     => tmp_left_in,
            DATA_OUT    => tmp_left_out,
            NUM_SHIFT   => tmp_shift(I),
            CE_IN       => '1',
            CE_OUT      => '1'
         );

         -- DSP comparator: compare NUM_SHIFT and null
         DSP_CMP_inst : entity work.CMP_DSP(structural)
         generic map (
            DATA_WIDTH   => 16,
            REG_IN       => 0,
            REG_OUT      => 0
         )
         port map (
            CLK         => CLK,
            RESET       => '0',
            A           => tmp_shift(I),
            B           => (others => '0'),
            CE_IN       => '1',
            CE_OUT      => '1',
            P           => tmp_cmp(I)
         );

         -- generate NUM_SHIFTER signal
         process (num_shift_reg(15 + ((I-1) * 16)), tmp_cmp(I)(1))
         begin

            if (tmp_cmp(I)(1) = '1') then
               tmp_shift(I - 1)(15) <= num_shift_reg(15 + ((I-1) * 16));
            else
               tmp_shift(I - 1)(15) <= '1';
            end if;
         end process;

         tmp_shift(I - 1)(14 downto 0) <= num_shift_reg(15 + ((I-1) * 16) - 1 downto ((I - 1) * 16));
      end generate;
   end generate;

   GEN_DATA_FOR_LAST_SHIFTER: if(MAX_SHIFT_M = 0) generate
   begin
      tmp_shift(MAX_SHIFT_1) <= num_shift_reg(15 + (MAX_SHIFT_1 * 16) downto MAX_SHIFT_1 * 16);
      data_out_reg <= tmp_out(MAX_SHIFT_1);
   end generate;

   GEN_SHIFT_MOD: if (MAX_SHIFT_M > 0) generate
   begin
      --! generate one shifter when MAX_SHIFT < 16
      GEN_SHIFT_ONE: if(MAX_SHIFT < 16) generate
        signal tmp : std_logic_vector(15 downto 0);
      begin
         tmp <= zeros(15 - MAX_SHIFT downto 0) & num_shift_reg;

         GEN_DSP_SHIFTER_inst: entity work.GEN_DSP_SHIFTER(full)
         generic map (
            DATA_WIDTH => DATA_WIDTH,
            SHIFT_LEFT => SHIFT_LEFT,
            REG_IN   => REG_IN,
            REG_OUT  => REG_OUT,
            REG_OUT_WITH_DSP => REGS_WITH_DSP
         )
         port map (
            CLK         => CLK,
            RESET       => RESET,
            DATA_IN     => DATA_IN,
            DATA_OUT    => DATA_OUT,
            NUM_SHIFT   => tmp,
            CE_IN       => CE_IN,
            CE_OUT      => CE_OUT
         );
      end generate;

      --! generate last shifter when MAX_SHIFT mod 16 /= 0
      GEN_SHIFT_LAST: if(MAX_SHIFT > 16) generate
         signal tmp_left_in   : std_logic_vector(DATA_WIDTH - (MAX_SHIFT_D * 16) - 1 downto 0);
         signal tmp_left_out  : std_logic_vector(DATA_WIDTH - (MAX_SHIFT_D * 16) - 1 downto 0);
      begin
         -- generate left shifter
         GEN_LEFT_LAST: if(SHIFT_LEFT = true) generate
            tmp_left_in <= tmp_out(MAX_SHIFT_1)(DATA_WIDTH - 1 downto MAX_SHIFT_D * 16);
            tmp_out(MAX_SHIFT_D)((MAX_SHIFT_D * 16) - 1 downto 0) <= tmp_out(MAX_SHIFT_D - 1)((MAX_SHIFT_D * 16) - 1 downto 0);
            tmp_out(MAX_SHIFT_D)(DATA_WIDTH - 1 downto MAX_SHIFT_D * 16) <= tmp_left_out;
         end generate;

         -- generate right shifter
         GEN_RIGHT_LAST: if(SHIFT_LEFT = false) generate
            tmp_left_in <= tmp_out(MAX_SHIFT_1)(DATA_WIDTH - (MAX_SHIFT_D * 16) - 1 downto 0);
            tmp_out(MAX_SHIFT_D)(DATA_WIDTH - 1 downto DATA_WIDTH - (MAX_SHIFT_D * 16)) <= tmp_out(MAX_SHIFT_D - 1)(DATA_WIDTH - 1 downto DATA_WIDTH - (MAX_SHIFT_D * 16));
            tmp_out(MAX_SHIFT_D)(DATA_WIDTH - (MAX_SHIFT_D * 16) - 1 downto 0) <= tmp_left_out;
         end generate;

         -- connect shifter
         GEN_DSP_SHIFTER_inst: entity work.GEN_DSP_SHIFTER(full)
         generic map (
            DATA_WIDTH => DATA_WIDTH - (MAX_SHIFT_D * 16),
            SHIFT_LEFT => SHIFT_LEFT,
            REG_IN   => 0,
            REG_OUT  => 0
         )
         port map (
            CLK         => CLK,
            RESET       => RESET,
            DATA_IN     => tmp_left_in,
            DATA_OUT    => tmp_left_out,
            NUM_SHIFT   => tmp_shift(MAX_SHIFT_D),
            CE_IN       => '1',
            CE_OUT      => '1'
         );

         DSP_CMP_inst : entity work.CMP_DSP(structural)
         generic map (
            DATA_WIDTH   => MAX_SHIFT_M,
            REG_IN       => 0,
            REG_OUT      => 0
         )
         port map (
            CLK         => CLK,
            RESET       => '0',
            A           => num_shift_reg(MAX_SHIFT - 1 downto MAX_SHIFT - MAX_SHIFT_M),
            B           => (others => '0'),
            CE_IN       => '1',
            CE_OUT      => '1',
            P           => tmp_cmp(MAX_SHIFT_D)
         );

         process (num_shift_reg(15 + (MAX_SHIFT_1 * 16)), tmp_cmp(MAX_SHIFT_D)(1))
         begin
            if (tmp_cmp(MAX_SHIFT_D)(1) = '1') then
               tmp_shift(MAX_SHIFT_1)(15) <= num_shift_reg(15 + (MAX_SHIFT_1 * 16));
            else
               tmp_shift(MAX_SHIFT_1)(15) <= '1';
            end if;
         end process;
         tmp_shift(MAX_SHIFT_1)(14 downto 0) <= num_shift_reg(15 + (MAX_SHIFT_1 * 16) - 1 downto (MAX_SHIFT_1 * 16));

         tmp_shift(MAX_SHIFT_D) <= zeros(15 - MAX_SHIFT_M downto 0) & num_shift_reg(MAX_SHIFT - 1 downto MAX_SHIFT - MAX_SHIFT_M);
         data_out_reg <= tmp_out(MAX_SHIFT_D);
      end generate;
   end generate;

end architecture;
