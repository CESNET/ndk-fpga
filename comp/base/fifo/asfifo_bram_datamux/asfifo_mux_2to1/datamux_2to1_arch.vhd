-- datamux_2to1_arch.vhd
--!
--! \file
--! \brief Asynchronous fifo mutiplex in BRAMs for Xilinx FPGAs
--! \author Ondrej Dujiček <xdujic02@stud.feec.vutbr.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
--! Package with log2 function.




-- ----------------------------------------------------------------------------
--                       Architecture declaration
-- ----------------------------------------------------------------------------


architecture FULL of ASFIFO_MUX_2TO1 is


   --! Constant declaration
  constant  DATA_HALF_WIDTH         : integer :=INPUT_DATA_WIDTH/2;
   --! Signals declaration
   signal rd_en    		            : std_logic;
   signal rd_h                      : std_logic;
   signal data_out                  : std_logic_vector (INPUT_DATA_WIDTH-1 downto 0);
   signal fifo_out                  : std_logic_vector (INPUT_DATA_WIDTH downto 0);
   signal fifo_empty                : std_logic;
   signal fifo_dv                   : std_logic;
   signal fifo_in                   : std_logic_vector (INPUT_DATA_WIDTH downto 0);
   type t_state is (LOW, HIGH );
   signal present_state, next_state : t_state;
-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------

begin -------------------------------------------------------------------------

  asfifo : entity work.ASFIFO_BRAM_XILINX
   generic map(
      DEVICE                  => DEVICE,
      DATA_WIDTH              => INPUT_DATA_WIDTH+1,
      ITEMS                   => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET ,  --
      ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK_WR         => CLK_WR,
      RST_WR         => RST_WR,
      DI             => fifo_in,
      WR             => WR,
      FULL           => FULL,
      AFULL          => AFULL,

      CLK_RD         => CLK_RD,
      RST_RD         => RST_RD,
      DO             => fifo_out,
      RD             => rd_en,
      EMPTY          => fifo_empty,
      AEMPTY         => AEMPTY
   );

   -------------------------------------------------------------------
   fifo_in       <= DI & WR_H;
   data_out      <= fifo_out(INPUT_DATA_WIDTH downto 1);
   rd_h          <= fifo_out (0);
   fifo_dv       <= not fifo_empty;
   EMPTY         <= fifo_empty;
   DO_VLD        <= fifo_dv;
   -------------------------------------------------------------------


   sync_datamux: process(CLK_RD)
   begin
   if (rising_edge (CLK_RD)) then
      if (RST_RD = '1') then
         present_state <= LOW;
      elsif (RD ='1'and fifo_dv ='1') then
         present_state <= next_state;
      else
         present_state <= LOW;
      end if;
   end if ;
   end process;

   -- -------------------------------------------------------------------------
   next_state_logic: process(present_state, rd_h)
   begin
      case (present_state) is
      when LOW =>

         if (rd_h = '1') then
          next_state <= HIGH;
          rd_en <= '0';
         else
            next_state <= LOW;
            rd_en <= '1';
         end if ;

      when HIGH =>
      	rd_en <= '1';
      	next_state <= LOW;

      when others =>
      	next_state <= LOW;
         rd_en <= '0';
      -- - - - - - - - - - - - - - - - - - - - -
      end case;
   end process;


   -- -------------------------------------------------------------------------
   output_logic: process(present_state, data_out)
   begin
    	 DO <= data_out (DATA_HALF_WIDTH-1 downto 0);
      case (present_state) is
      when LOW =>                                       ---- lower part of word
     	 DO <= data_out (DATA_HALF_WIDTH-1 downto 0);

      when HIGH =>                                       ---- upper part of word
       DO <= data_out (INPUT_DATA_WIDTH-1 downto DATA_HALF_WIDTH);
      -- - - - - - - - - - - - - - - - - - - - -
      when others =>
      -- - - - - - - - - - - - - - - - - - - - -
      end case;
   end process;

end architecture FULL;
