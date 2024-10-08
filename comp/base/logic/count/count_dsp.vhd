--! count_dsp.vhd
--!
--! \file
--! \brief counter implemented with Virtex-7 DSP slices
--! \author Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

architecture structural of COUNT_DSP is
   signal enable_p         :std_logic_vector(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1))) downto 0);
   signal a_p              :std_logic_vector(DATA_WIDTH-1 downto 0);
   signal max_p            :std_logic_vector(DATA_WIDTH-1 downto 0);

   signal reset_all        : std_logic;
   signal in_out_Vector    : std_logic_vector ((DATA_WIDTH/48) downto 0);
   signal pattern_all      : std_logic_vector (((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)) - 1) downto 0);
   signal temp             : std_logic;

   signal reg_cnt          : std_logic_vector(DATA_WIDTH-1 downto 0);
begin
   GEN_DSP_OFF: if(DSP_EN = false) generate
      signal ENABLE_REG : std_logic;
      signal A_REG      : std_logic_vector(DATA_WIDTH-1 downto 0);
      signal MAX_REG    : std_logic_vector(DATA_WIDTH-1 downto 0);
   begin
      GEN_INPUT_PIPE_ON: if(REG_IN = 1) generate
         PIPE : process(CLK)
         begin
            if (CLK'event and CLK='1') then
               if RESET='1' then
                  A_REG       <= (others => '0');
                  MAX_REG     <= (others => '0');
                  ENABLE_REG  <= '0';
               else
                  A_REG       <= A;
                  MAX_REG     <= MAX;
                  ENABLE_REG  <= ENABLE;
               end if;
            end if;
         end process;
      end generate;

      GEN_INPUT_PIPE_OFF: if(REG_IN = 0) generate
         A_REG       <= A;
         MAX_REG     <= MAX;
         ENABLE_REG  <= ENABLE;
      end generate;

      GEN_AUTO_RESET_OFF: if(AUTO_RESET = 0) generate
         up_cnt_gen : if DIR=true generate
            cnt : process(CLK)
            begin
               if (CLK'event and CLK='1') then
                  if RESET = '1' then
                     reg_cnt <= (others => '0');
                  elsif ENABLE_REG='1' then
                     reg_cnt <= std_logic_vector(unsigned(reg_cnt)+unsigned(A_REG));
                  end if;
               end if;
            end process;
         end generate;

         down_cnt_gen : if DIR=false generate
            cnt : process(CLK)
            begin
               if (CLK'event and CLK='1') then
                  if RESET = '1' then
                     reg_cnt <= (others => '0');
                  elsif ENABLE_REG='1' then
                     reg_cnt <= std_logic_vector(unsigned(reg_cnt)-unsigned(A_REG));
                  end if;
               end if;
            end process;
         end generate;
      end generate;

      GEN_AUTO_RESET_ON: if(AUTO_RESET = 1) generate
         up_cnt_gen : if DIR=true generate
            cnt : process(CLK)
            begin
               if (CLK'event and CLK='1') then
                  if RESET = '1' or (MAX_REG <= reg_cnt) then
                     reg_cnt <= (others => '0');
                  elsif ENABLE_REG='1' then
                     reg_cnt <= std_logic_vector(unsigned(reg_cnt)+unsigned(A_REG));
                  end if;
               end if;
            end process;
         end generate;

         down_cnt_gen : if DIR=false generate
            cnt : process(CLK)
            begin
               if (CLK'event and CLK='1') then
                  if RESET = '1' or MAX_REG <= reg_cnt then
                     reg_cnt <= (others => '0');
                  elsif ENABLE_REG='1' then
                     reg_cnt <= std_logic_vector(unsigned(reg_cnt)-unsigned(A_REG));
                  end if;
               end if;
            end process;
         end generate;
      end generate;
      P <= reg_cnt;
   end generate;



   GEN_DSP_ON: if(DSP_EN = true) generate
      --! generate input registers
      GEN_IN_REG: if(REG_IN = 1 AND DATA_WIDTH > 48) generate
         process(CLK)
         begin
            if(CLK'event) and (CLK='1') then
               --if (ENABLE = '1') then
                  a_p(DATA_WIDTH-1 downto 48) <= A(DATA_WIDTH-1 downto 48);
               --end if;
            end if;
         end process;

         --! when auto reset is ON
         GEN_MAX_RESET: if(AUTO_RESET = 1) generate
            process(CLK)
            begin
               if(CLK'event) and (CLK='1') then
                  --if (ENABLE = '1') then
                     max_p(DATA_WIDTH-1 downto 48) <= MAX(DATA_WIDTH-1 downto 48);
                  --end if;
               end if;
            end process;
         end generate;

         --! when auto reset is OFF
         GEN_MAX_NO_RESET: if(AUTO_RESET = 0) generate
            max_p <= MAX;
         end generate;
      end generate;

      GEN_NO_IN_REG: if(REG_IN = 0 OR DATA_WIDTH <= 48) generate
         a_p <= A;
         max_p <= MAX;
      end generate;

      enable_p(0) <= ENABLE;

      GEN_REG_EN: for I in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)))-1 generate
         process(CLK)
            begin
               if(CLK'event) and (CLK='1') then
                  if (RESET='1') then
                     enable_p(I+1) <= '0';
                  else
                     enable_p(I+1) <= enable_p(I);
                  end if;
               end if;
            end process;
      end generate;

      --! generate pattern logic
      GEN_RST_LOGIC: if (AUTO_RESET = 1) generate
         process(pattern_all)
            variable o : std_logic;
         begin
            o := '1';
            for I in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)) - 1) loop
               o := o and pattern_all(I);
            end loop;
              temp <= o;
         end process;

         GEN_RST_LOGIC: if(DATA_WIDTH > 48) generate
            process(temp, RESET)
            begin
               if (temp = '1' OR (RESET = '1')) then
                  reset_all <= '1';
               else
                  reset_all <= '0';
               end if;
            end process;
         end generate;
      end generate;

      GEN_RTS_NO_LOGIC: if(DATA_WIDTH <= 48 or AUTO_RESET = 0) generate
         reset_all <= RESET;
      end generate;

      --! first carryin value
      in_out_Vector(0) <= '0';

      GEN_COUNT_DIV: for I in 0 to (DATA_WIDTH/48)-1 generate
         --! DSP for only 48 bit
         GEN_ONE_DSP_48: if(DATA_WIDTH = 48) generate
            GEN_RESET_OFF: if(AUTO_RESET = 0) generate
               COUNT48_inst: entity work.COUNT48
                  generic map(
                     REG_IN  => REG_IN,
                     AUTO_RESET => "NO_RESET",
                     DEVICE => DEVICE,
                     CARRY_SEL => 0
                  )
                  port map (
                     CLK => CLK,
                     ENABLE => enable_p(0),
                     ENABLE_IN => enable_p(0),
                     RESET => reset_all,
                     RESET_OUT => reset_all,
                     CAS_CARRY_IN => '0',
                     A => a_p(47+I*48 downto 0+I*48),
                     MAX => max_p(47+I*48 downto 0+I*48),
                     P => P(47+I*48 downto 0+I*48),
                     CAS_CARRY_OUT => open,
                     PATTERN => open
                  );
            end generate;

            GEN_RESET_ON: if(AUTO_RESET = 1) generate
               COUNT48_inst: entity work.COUNT48
                  generic map(
                     REG_IN  => REG_IN,
                     AUTO_RESET => "RESET_MATCH",
                     DEVICE => DEVICE,
                     CARRY_SEL => 0
                  )
                  port map (
                     CLK => CLK,
                     ENABLE => enable_p(0),
                     ENABLE_IN => enable_p(0),
                     RESET => reset_all,
                     RESET_OUT => reset_all,
                     CAS_CARRY_IN => '0',
                     A => a_p(47+I*48 downto 0+I*48),
                     MAX => max_p(47+I*48 downto 0+I*48),
                     P => P(47+I*48 downto 0+I*48),
                     CAS_CARRY_OUT => open,
                     PATTERN => open
               );
            end generate;

         end generate;

         --! generate first DPS when DATA_WIDTH > 48
         GEN_FIRST_DSP: if(I = 0 and DATA_WIDTH /= 48) generate
            signal pattern_pom  : std_logic_vector(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1) downto 0);

            type array_pom_out_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1)) of std_logic_vector(47 downto 0);
            signal array_pom_out : array_pom_out_t;
         begin
            --! generate output registers
            GEN_REG_OUT: for I in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2) generate
               process(CLK)
               begin
                  if(CLK'event) and (CLK='1') then
                     --if (enable_p(2+I) = '1') then
                        array_pom_out(I + 1) <= array_pom_out(I);
                     --end if;
                  end if;
               end process;
            end generate;

            --! generate registers for DSP pattern output
            GEN_RST_LOGIC: if (AUTO_RESET = 1) generate
               GEN_REG_OUT: for I in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2) generate
                  process(CLK)
                  begin
                     if(CLK'event) and (CLK='1') then
                        --if (enable_p(2+I) = '1') then
                           pattern_pom(I + 1) <= pattern_pom(I);
                        --end if;
                     end if;
                  end process;
               end generate;
            end generate;

            P(47+I*48 downto 0+I*48) <= array_pom_out((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1);
            pattern_all(I) <= pattern_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1));

            COUNT48_inst: entity work.COUNT48
            generic map(
               REG_IN  => REG_IN * 3,
               AUTO_RESET => "NO_RESET",
               CARRY_SEL => 0
            )
            port map (
               CLK => CLK,
               ENABLE => enable_p(1),
               ENABLE_IN => enable_p(0),
               RESET => RESET,
               RESET_OUT => reset_all,
               CAS_CARRY_IN => in_out_vector(0),
               A => A(47+I*48 downto 0+I*48),
               MAX => MAX(47+I*48 downto 0+I*48),
               P => array_pom_out(0),
               CAS_CARRY_OUT => in_out_vector(1),
               PATTERN => pattern_pom(0)
            );
         end generate;

         --! generate DSPs between first and last
         GEN_DSP_BETWEEN: if((I > 0) and ((I < ((DATA_WIDTH/48) -1)) OR ((DATA_WIDTH mod 48) > 0))) generate
            signal pattern_pom  : std_logic_vector(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1 - I) downto 0);

            type array_pom_out_t is array (0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 1 - I)) of std_logic_vector(47 downto 0);
            signal array_pom_out : array_pom_out_t;

            type array_pom_in_t is array (0 to I - 1) of std_logic_vector(47 downto 0);
            signal array_pom_in_A   : array_pom_in_t;
            signal array_pom_in_MAX : array_pom_in_t;
         begin

            GEN_REG_OUT: for Y in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2 - I) generate
               process(CLK)
               begin
                  if(CLK'event) and (CLK='1') then
                     --if (enable_p(I+2+Y) = '1') then
                        array_pom_out(Y + 1) <= array_pom_out(Y);
                     --end if;
                  end if;
               end process;
            end generate;

            GEN_RST_LOGIC: if (AUTO_RESET = 1) generate
               GEN_REG_OUT: for Y in 0 to ((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - 2 - I) generate
                  process(CLK)
                  begin
                     if(CLK'event) and (CLK='1') then
                        --if (enable_p(I+2+Y) = '1') then
                           pattern_pom(Y + 1) <= pattern_pom(Y);
                        --end if;
                     end if;
                  end process;
               end generate;
            end generate;

            --! generate input registers for signal A
            GEN_REG_IN_A: for Y in 0 to (I - 2) generate
               process(CLK)
               begin
                  if(CLK'event) and (CLK='1') then
                     --if (enable_p(1+Y) = '1') then
                        array_pom_in_A(Y + 1) <= array_pom_in_A(Y);
                     --end if;
                  end if;
               end process;
            end generate;

            --! generate input registers for signal MAX
            GEN_REG_IN_MAX: if (AUTO_RESET = 1) generate
               GEN_REG_IN: for Y in 0 to (I - 2) generate
                  process(CLK)
                  begin
                     if(CLK'event) and (CLK='1') then
                        --if (enable_p(1+Y) = '1') then
                           array_pom_in_MAX(Y + 1) <= array_pom_in_MAX(Y);
                        --end if;
                     end if;
                  end process;
               end generate;
            end generate;

            GEN_CON_MAX: if (AUTO_RESET = 0) generate
               array_pom_in_MAX(I - 1) <= array_pom_in_MAX(0);
            end generate;

            array_pom_in_A(0) <= a_p(47+I*48 downto 0+I*48);
            array_pom_in_MAX(0) <= max_p(47+I*48 downto 0+I*48);

            P(47+I*48 downto 0+I*48) <= array_pom_out((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - I - 1);
            pattern_all(I) <= pattern_pom(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) +1)) - I - 1));

            COUNT48_inst: entity work.COUNT48
            generic map(
               REG_IN  => 3,
               AUTO_RESET => "NO_RESET"
            )
            port map (
               CLK => CLK,
               ENABLE => enable_p(I + 1),
               ENABLE_IN => enable_p(I),
               RESET => reset_all,
               RESET_OUT => reset_all,
               CAS_CARRY_IN => in_out_vector(I),
               A => array_pom_in_A(I - 1),
               MAX => array_pom_in_MAX(I - 1),
               P => array_pom_out(0),
               CAS_CARRY_OUT => in_out_vector(I + 1),
               PATTERN => pattern_pom(0)
            );
         end generate;

         --! generate last DSP when DATA_WIDTH mod 48 is 0
         GEN_DSP_LAST: if((I > 0) and I = ((DATA_WIDTH/48) - 1) and (DATA_WIDTH mod 48) = 0) generate
            type array_pom_in_t is array (0 to I - 1) of std_logic_vector(47 downto 0);
            signal array_pom_in_A   : array_pom_in_t;
            signal array_pom_in_MAX : array_pom_in_t;
         begin
            GEN_REG_IN_A: for Y in 0 to (I - 2) generate
               process(CLK)
               begin
                  if(CLK'event) and (CLK='1') then
                     --if (enable_p(1+Y) = '1') then
                        array_pom_in_A(Y + 1) <= array_pom_in_A(Y);
                     --end if;
                  end if;
               end process;
            end generate;

            GEN_REG_IN_MAX: if (AUTO_RESET = 1) generate
               GEN_REG_IN: for Y in 0 to (I - 2) generate
                  process(CLK)
                  begin
                     if(CLK'event) and (CLK='1') then
                        --if (enable_p(1+Y) = '1') then
                           array_pom_in_MAX(Y + 1) <= array_pom_in_MAX(Y);
                        --end if;
                     end if;
                  end process;
               end generate;
            end generate;

            array_pom_in_A(0) <= a_p(47+I*48 downto 0+I*48);
            array_pom_in_MAX(0) <= max_p(47+I*48 downto 0+I*48);

            COUNT48_inst: entity work.COUNT48
            generic map(
               REG_IN  => 3,
               AUTO_RESET => "NO_RESET"
            )
            port map (
               CLK => CLK,
               ENABLE => enable_p(I + 1),
               ENABLE_IN => enable_p(I),
               RESET => reset_all,
               RESET_OUT => reset_all,
               CAS_CARRY_IN => in_out_vector(I),
               A => array_pom_in_A(I - 1),
               MAX => array_pom_in_MAX(I - 1),
               P => P(47+I*48 downto 0+I*48),
               CAS_CARRY_OUT => open,
               PATTERN    => pattern_all(I)
            );
         end generate;
      end generate;

      --! generate last DSP when DATA_WIDTH mod 48 /= 0 and generate one DSP when DATA_WIDTH < 48
      GEN_COUNT_MOD: if (DATA_WIDTH mod 48 > 0) generate
         signal Amod : std_logic_vector(47 downto 0);
         signal Bmod : std_logic_vector(47 downto 0);
         signal Pmod : std_logic_vector(47 downto 0);

         type array_pom_in_t is array (0 to (DATA_WIDTH/48) - 1) of std_logic_vector((DATA_WIDTH mod 48)-1 downto 0);
         signal array_pom_in_A   : array_pom_in_t;
         signal array_pom_in_MAX : array_pom_in_t;
      begin
         GEN_REG_IN_A: for Y in 0 to ((DATA_WIDTH/48) - 2) generate
            process(CLK)
            begin
               if(CLK'event) and (CLK='1') then
                  --if (enable_p(1+Y) = '1') then
                     array_pom_in_A(Y + 1) <= array_pom_in_A(Y);
                  --end if;
               end if;
            end process;
         end generate;

         GEN_REG_IN_MAX: if (AUTO_RESET = 1) generate
            GEN_REG_IN: for Y in 0 to ((DATA_WIDTH/48) - 2) generate
               process(CLK)
               begin
                  if(CLK'event) and (CLK='1') then
                     --if (enable_p(1+Y) = '1') then
                        array_pom_in_MAX(Y + 1) <= array_pom_in_MAX(Y);
                     --end if;
                  end if;
               end process;
            end generate;
         end generate;

         GEN_LAST_DSP: if(DATA_WIDTH > 48) generate
            array_pom_in_A(0) <= a_p(a_p'LENGTH-1 downto a_p'LENGTH-1-(DATA_WIDTH mod 48)+1);
            array_pom_in_MAX(0) <= max_p(max_p'LENGTH-1 downto max_p'LENGTH-1-(DATA_WIDTH mod 48)+1);

            Amod((DATA_WIDTH mod 48)-1 downto 0) <= array_pom_in_A(DATA_WIDTH/48 - 1);
            Bmod((DATA_WIDTH mod 48)-1 downto 0) <= array_pom_in_MAX(DATA_WIDTH/48 - 1);
         end generate;

         GEN_ONE_DSP: if(DATA_WIDTH < 48) generate
            Amod((DATA_WIDTH mod 48)-1 downto 0) <= a_p(a_p'LENGTH-1 downto a_p'LENGTH-1-(DATA_WIDTH mod 48)+1);
            Bmod((DATA_WIDTH mod 48)-1 downto 0) <= max_p(max_p'LENGTH-1 downto max_p'LENGTH-1-(DATA_WIDTH mod 48)+1);
         end generate;

         Amod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');
         Bmod(47 downto (DATA_WIDTH mod 48)) <= (others => '0');

         --! when DATA_WIDTH < 48
         GEN_DSP_ONE: if(DATA_WIDTH < 48) generate
            GEN_RESET_OFF: if(AUTO_RESET = 0) generate
               COUNT48_inst: entity work.COUNT48
               generic map(
                  REG_IN  => REG_IN,
                  AUTO_RESET => "NO_RESET",
                  CARRY_SEL => 0
               )
               port map (
                  CLK => CLK,
                  ENABLE => enable_p(0),
                  ENABLE_IN => enable_p(0),
                  RESET => reset_all,
                  RESET_OUT => reset_all,
                  CAS_CARRY_IN => '0',
                  A =>  Amod,
                  MAX => Bmod,
                  P => Pmod,
                  CAS_CARRY_OUT => open,
                  PATTERN => open
               );
            end generate;

            GEN_RESET_ON: if(AUTO_RESET = 1) generate
               COUNT48_inst: entity work.COUNT48
               generic map(
                  REG_IN  => REG_IN,
                  AUTO_RESET => "RESET_MATCH",
                  CARRY_SEL => 0
               )
               port map (
                  CLK => CLK,
                  ENABLE => enable_p(0),
                  ENABLE_IN => enable_p(0),
                  RESET => reset_all,
                  RESET_OUT => reset_all,
                  CAS_CARRY_IN => '0',
                  A =>  Amod,
                  MAX => Bmod,
                  P => Pmod,
                  CAS_CARRY_OUT => open,
                  PATTERN => open
               );
            end generate;
         end generate;

         --! last DSP
         GEN_DSP_LAST: if(DATA_WIDTH > 48) generate
            COUNT48_inst: entity work.COUNT48
            generic map(
               REG_IN  => 3,
               AUTO_RESET => "NO_RESET"
            )
            port map (
               CLK => CLK,
               ENABLE => enable_p(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)))),
               ENABLE_IN => enable_p(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)))-1),
               RESET => reset_all,
               RESET_OUT => reset_all,
               CAS_CARRY_IN => in_out_Vector(DATA_WIDTH/48),
               A => Amod,
               MAX => Bmod,
               P => Pmod,
               CAS_CARRY_OUT => open,
               PATTERN => pattern_all(((DATA_WIDTH/48) + (1 mod ((DATA_WIDTH mod 48) + 1)) - 1))
            );
         end generate;

         P(P'LENGTH-1 downto P'LENGTH-1-(DATA_WIDTH mod 48)+1) <= Pmod((DATA_WIDTH mod 48)-1 downto 0);

      end generate;
   end generate;
end architecture;
