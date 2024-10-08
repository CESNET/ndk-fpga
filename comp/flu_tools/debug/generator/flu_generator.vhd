-- flu_generator.vhd: Simple FLU frame generator
-- Copyright (C) 2017 CESNET
-- Author(s): Martin Spinler <spinler@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

library work;
use work.math_pack.all;

-- -----------------------------------------------------------------------------
--                              Entity declaration
-- -----------------------------------------------------------------------------

entity FLU_GENERATOR is
   generic (
      --! Number of RX DMA channels
      CHANNELS          : integer := 8;
      --! Input FrameLink width in bits
      FLU_WIDTH         : integer := 512;
      --! Input FLU SOP width
      SOP_WIDTH         : integer := 3
   );
   port (
      --! Common interface
      CLK               : in  std_logic;
      RESET             : in  std_logic;

      --! Output FLU interface
      FLU_CHANNEL       : out std_logic_vector(log2(CHANNELS)-1 downto 0);
      FLU_DATA          : out std_logic_vector(FLU_WIDTH-1 downto 0);
      FLU_SOP_POS       : out std_logic_vector(SOP_WIDTH-1 downto 0);
      FLU_EOP_POS       : out std_logic_vector(log2(FLU_WIDTH/8)-1 downto 0);
      FLU_SOP           : out std_logic;
      FLU_EOP           : out std_logic;
      FLU_SRC_RDY       : out std_logic;
      FLU_DST_RDY       : in  std_logic;

      --! SW Access for configuration
      MI_ADDR           : in  std_logic_vector(31 downto 0);
      MI_DWR            : in  std_logic_vector(31 downto 0);
      MI_BE             : in  std_logic_vector(3 downto 0);
      MI_RD             : in  std_logic;
      MI_WR             : in  std_logic;
      MI_DRD            : out std_logic_vector(31 downto 0);
      MI_ARDY           : out std_logic;
      MI_DRDY           : out std_logic
   );
end entity FLU_GENERATOR;

-- -----------------------------------------------------------------------------
--                           Architecture declaration
-- -----------------------------------------------------------------------------

architecture full of FLU_GENERATOR is

   constant WORDS                   : integer := 2**SOP_WIDTH;
   constant MI_WIDTH                : integer := 32;

   type   t_send_state              is (S_IDLE, S_PACKET);
   signal gen_present_state         : t_send_state := S_IDLE;
   signal gen_next_state            : t_send_state;
   signal generator_cntr            : std_logic_vector(31 downto 0) := (others => '0');
   signal generator_cntr_en         : std_logic;
   signal generator_run             : std_logic := '0';
   signal generator_length          : std_logic_vector(15 downto 0);
   signal generator_rem             : std_logic_vector(15-3 downto 0);
   signal generator_words           : std_logic_vector(15-3 downto 0);
   signal generator_chmax           : std_logic_vector(log2(CHANNELS) downto 0) := (others => '0');

begin

   MI_DRDY     <= MI_RD;
   MI_ARDY     <= MI_RD or MI_WR;

   with MI_ADDR(2) select MI_DRD <=
      (MI_WIDTH-1 downto log2(CHANNELS)+1 => '0')  & generator_chmax + 1     when '0',
      (MI_WIDTH-1 downto 16 => '0')                & generator_length        when '1',
                                                     X"00000000"             when others;

   control_p: process(CLK)
   begin
      if CLK = '1' and CLK'event then
         if (RESET = '1') then
            generator_run <= '0';
         end if;

         if(MI_WR = '1' and MI_ADDR(2) = '0') then
            generator_chmax      <= MI_DWR(log2(CHANNELS) downto 0) - 1;
            generator_cntr_en    <= MI_DWR(31);

            if(MI_DWR(3 downto 0) = 0) then
               generator_run     <= '0';
            else
               generator_run     <= '1';
               generator_cntr    <= (others => '0');
            end if;
         end if;

         if(MI_WR = '1' and MI_ADDR(2) = '1') then
            generator_length     <= MI_DWR(15 downto 0);
            if(MI_DWR(2 downto 0) = 0) then
               generator_words   <= MI_DWR(15 downto 3);
            else
               generator_words   <= MI_DWR(15 downto 3) + 1;
            end if;
         end if;

         if(generator_run = '1' and FLU_DST_RDY = '1' and FLU_SOP = '1') then
            if(generator_cntr_en = '1') then
               generator_cntr <= generator_cntr + 1;
            end if;

            if(FLU_CHANNEL < generator_chmax) then
               FLU_CHANNEL <= FLU_CHANNEL + 1;
            else
               FLU_CHANNEL <= (others => '0');
            end if;
         end if;
      end if;
   end process;

   gen_rx_data : for i in 0 to 7 generate
      FLU_DATA(64*(i+1)-1 downto 64*i) <= (generator_cntr & X"0000" & generator_length) when FLU_SOP = '1' and FLU_SOP_POS = i else (others => '0');
   end generate;

   sync_logic : process(CLK)
   begin
      if(CLK'event AND CLK = '1') then
         gen_present_state              <= gen_next_state;
      end if;
   end process sync_logic;

   gen_next_state_logic : process (gen_present_state, FLU_DST_RDY, generator_run, generator_rem, generator_words)
   begin
      gen_next_state                    <= gen_present_state;

      case (gen_present_state) is
         -- ---------------------------------------------
         when S_IDLE =>
            if(FLU_DST_RDY = '1' and generator_run = '1') then
               gen_next_state           <= S_PACKET;

               if(generator_words <= WORDS) then
                  gen_next_state        <= S_IDLE;
               end if;
            end if;
         -- ---------------------------------------------
         when S_PACKET =>
            if(FLU_DST_RDY = '1') then
               if   (generator_rem = WORDS) then
                  gen_next_state        <= S_IDLE;
               elsif(generator_rem < WORDS) then
                  gen_next_state        <= S_IDLE;

                  if(generator_run = '1') then
                     gen_next_state     <= S_PACKET;
                  end if;
               end if;
            end if;
         -- ---------------------------------------------
         when others =>
            gen_next_state              <= S_IDLE;
         -- ---------------------------------------------
      end case;
   end process;

   output_logic : process (gen_present_state, FLU_DST_RDY, generator_rem, generator_words, generator_run, generator_length, generator_cntr)
   begin
      FLU_SRC_RDY                       <= '0';
      FLU_SOP                           <= '0';
      FLU_EOP                           <= '0';

      FLU_SOP_POS                       <= generator_rem(SOP_WIDTH-1 downto 0);
      FLU_EOP_POS(SOP_WIDTH+2 downto 3) <= generator_rem(SOP_WIDTH-1 downto 0) - 1;
      FLU_EOP_POS(2 downto 0)           <= generator_length(2 downto 0) - 1;

      case (gen_present_state) is
         -- ---------------------------------------------
         when S_IDLE =>
            FLU_SOP                     <= '1';
            FLU_SOP_POS                 <= (others => '0');
            FLU_SRC_RDY                 <= generator_run;

            if(generator_words <= WORDS) then
               FLU_EOP                  <= '1';
               FLU_EOP_POS(SOP_WIDTH+2 downto 3) <= generator_words(SOP_WIDTH-1 downto 0) - 1;
            end if;
         -- ---------------------------------------------
         when S_PACKET =>
            FLU_SRC_RDY                 <= '1';

            if   (generator_rem = WORDS) then
               FLU_EOP                  <= '1';
            elsif(generator_rem < WORDS) then
               FLU_EOP                  <= '1';

               if(generator_run = '1') then
                  FLU_SOP               <= '1';
               end if;
            end if;
         -- ---------------------------------------------
         when others =>
         -- ---------------------------------------------
      end case;
   end process;

   reg_send_fsm : process(CLK)
   begin
      if(CLK'event AND CLK = '1') then
         if(gen_present_state = S_IDLE) then
            generator_rem              <= generator_words - WORDS;
         elsif(gen_present_state = S_PACKET) then
            if(FLU_DST_RDY = '1') then
               generator_rem           <= generator_rem - WORDS;
               if(generator_rem < WORDS) then
                  generator_rem        <= generator_words - generator_rem;
                  if(generator_run = '1') then
                     if(generator_words > WORDS - generator_rem) then
                        generator_rem  <= generator_words - (WORDS - generator_rem);
                     end if;
                  end if;
               end if;
            end if;
         end if;
      end if;
   end process;
end architecture;

