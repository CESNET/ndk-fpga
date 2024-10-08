--! \file:   generator.vhd
--! \brief:  Generated Output data depending on the configuration
--! \Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--! \date 2014
--!
--! \section License
--!
--! Copyright (C) 2014 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

use IEEE.numeric_std.all;
Library UNISIM;
use UNISIM.vcomponents.all;
use work.math_pack.all;

entity GENERATOR is
   generic (
      --! Data width of input/output value
      DATA_WIDTH   : integer := 32;
      --! Number of items in memory
      ITEMS        : integer := 32;
      --! Data width of counters for generated SRC_RDY
      CNT_WIDTH    : integer := 0;
      --! Random generated SRC_RDY support
      RANDOM       : boolean := true
   );
   port (
      --! Clock input
      CLK      : in  std_logic;
      --! Reset input
      RESET    : in  std_logic;

      --! BRAM data
      BRAM_DATA  : in  std_logic_vector(32*div_roundup(DATA_WIDTH, 32)-1 downto 0);
      BRAM_RD    : out std_logic;
      BRAM_ADDR  : out std_logic_vector(log2(ITEMS)-1 downto 0);

      --! Data out
      DATA_OUT   : out  std_logic_vector(DATA_WIDTH - 1 downto 0);

      --! ready signals
      SRC_RDY  : out  std_logic;
      DST_RDY  : in  std_logic;

      --! Config Data
      CONFIG_1                    : in  std_logic_vector(31 downto 0);
      CONFIG_2                    : in  std_logic_vector(31 downto 0);
      CONFIG_3                    : in  std_logic_vector(31 downto 0);
      CONFIG_4                    : in  std_logic_vector(31 downto 0);

      --! Commands
      CMD_RUN        : in  std_logic;
      CMD_RUN_OFF    : out std_logic
   );
end GENERATOR;

--! Vitrex-7 architecture of MUL48
architecture full of GENERATOR is
   --! commandsi
   signal src_out     : std_logic_vector(0 downto 0);
   signal run_off     : std_logic;
   --! values from config1
   signal words_rdy     : std_logic_vector(15 downto 0);

   signal repeat_value  : std_logic_vector(15 downto 0);
   --! counter - number of valid words in BRAM.
   signal cnt_words     : std_logic_vector(15 downto 0);
      --! number of generated data
   signal cnt_repeat     : std_logic_vector(15 downto 0);
   --! counter for SRC_RDY
   --! mode1
   signal cnt_src_on     : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal cnt_src_off    : std_logic_vector(CNT_WIDTH-1 downto 0);
   signal cnt_pom        : std_logic;
   signal src_mod_1      : std_logic;
   --! mode 2
   signal src_mod_2      : std_logic;
   signal rand_out       : std_logic_vector (15 downto 0);
   --! mux mode - 1,2,3
   signal src_mux        : std_logic_vector(2 downto 0);
   signal src_pipe       : std_logic;


begin
   --! data in BRAM
   words_rdy    <= CONFIG_1(15 downto 0);

   repeat_value <= CONFIG_1(31 downto 16);

   --! generate mode 1
   generated_src_mod1: process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1' or run_off='1') then
            cnt_src_on <= (others => '0');
            cnt_src_off <= (others => '0');
            cnt_pom <= '0';
            src_mod_1 <= '0';
         elsif (CMD_RUN='1' and DST_RDY = '1')  then
            if (cnt_pom = '0') then
               --! length of active src_rdy
               if (cnt_src_on = CONFIG_2(CNT_WIDTH-1 downto 0)-1) then
                  cnt_src_on <= (others => '0');
                  cnt_pom <= '1';
               else
                  cnt_src_on <= cnt_src_on + 1;
               end if;
               src_mod_1 <= '1';
            else
               --! length of deactive src_rdy
               if (cnt_src_off = CONFIG_3(CNT_WIDTH-1 downto 0)-1) then
                  cnt_src_off <= (others => '0');
                  cnt_pom <= '0';
               else
                  cnt_src_off <= cnt_src_off + 1;
               end if;
               src_mod_1 <= '0';
            end if;
        end if;
      end if;
   end process;

   --! generate mode 2
   generated_src_mod2: process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1' or run_off='1') then
            src_mod_2 <= '0';
         elsif (CMD_RUN='1' and DST_RDY = '1')  then
            --! random generate src_rdy
            if(CONFIG_4(31 downto 16) >= rand_out) then
               src_mod_2 <= '1';
            else
               src_mod_2 <= '0';
            end if;
        end if;
     end if;
   end process;

   --! mux mode - 1,2,3
   --! mode 1 - permanently active
   src_mux(0) <= CMD_RUN and (not run_off);
   src_mux(1) <= src_mod_1;
   src_mux(2) <= src_mod_2;

   GEN_MUX_inst : entity work.GEN_MUX
   generic map (
      DATA_WIDTH => 1,
      MUX_WIDTH  => 3   -- multiplexer width (number of inputs)
   )
   port map(
      DATA_IN    => src_mux,
      SEL        => CONFIG_4(1 downto 0),
      DATA_OUT   => src_out
   );

   pipe_src: process(CLK)
   begin
      if(CLK'event) and (CLK='1') then
         if (RESET='1' or run_off = '1') then
            src_pipe <= '0';
         elsif(DST_RDY = '1') then
            src_pipe <= src_out(0);
         end if;
      end if;
   end process;

   --! generating a number of values of the output
   generated_data_out: process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1' or run_off='1') then
            cnt_repeat <= (others => '0');
            run_off <= '0';
         elsif (CMD_RUN='1')  then
            if (src_out(0) = '1' and DST_RDY = '1') then
               if (cnt_repeat = (repeat_value) and (repeat_value /= 0)) then
                  run_off <= '1';
                  cnt_repeat <= (others => '0');
               else
                  run_off <= '0';
                  cnt_repeat <= cnt_repeat + 1;
               end if;
            end if;
         end if;
      end if;
   end process;

   --! rotation in BRAMs memory
   generated_bram_addr: process(CLK)
   begin
      if (CLK'event) and (CLK='1') then
         if (RESET='1' or run_off='1') then
            cnt_words <= (others => '0');
         elsif (CMD_RUN='1')  then
            if (src_out(0) = '1' and DST_RDY = '1') then
               if (cnt_words = (words_rdy-1)) then
                  cnt_words <= (others => '0');
               else
                  cnt_words <= cnt_words + 1;
               end if;
            end if;
         end if;
      end if;
   end process;

   --! control BRAM - interface B
   DATA_OUT <= BRAM_DATA(DATA_WIDTH-1 downto 0);
   BRAM_RD   <= '1';
   BRAM_ADDR <= cnt_words(log2(ITEMS)-1 downto 0);

   --! control RUN register
   CMD_RUN_OFF <= run_off;

   SRC_RDY <= src_pipe and (not run_off);

   --! random value generator
   RAND_GENERATOR_inst : entity work.RAND_GENERATOR
   generic map (
      DATA_WIDTH => 16
   )
   port map(
      CLK        => CLK,
      RAND_OUT   => rand_out
   );

end full;

