-- datamux_1to2_arch.vhd
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
architecture FULL of ASFIFO_MUX_1TO2 is
-------------------------------------------------------------------------------

   --! Constant declaration
   --! Constant declaration
  constant  DATA_HALF_WIDTH         : integer :=OUTPUT_DATA_WIDTH/2;
   --! Signals declaration
   signal wr_low                    : std_logic;
   signal wr_high                   : std_logic;
   signal full_l                    : std_logic;
   signal full_h                    : std_logic;
   signal afull_l                   : std_logic;
   signal afull_h                   : std_logic;
   signal empty_l                   : std_logic;
   signal empty_h                   : std_logic;
   signal aempty_l                  : std_logic;
   signal aempty_h                  : std_logic;
   signal data_high                 : std_logic_vector (DATA_HALF_WIDTH downto 0);
   signal data_low                  : std_logic_vector (DATA_HALF_WIDTH downto 0);
   signal fifo_in                   : std_logic_vector (OUTPUT_DATA_WIDTH downto 0);
   signal fifo_out_l                : std_logic_vector (DATA_HALF_WIDTH downto 0);
   signal fifo_out_h                : std_logic_vector (DATA_HALF_WIDTH downto 0);

   type t_state is (WRIGHTING_LOW, WRIGHTING_HIGH );
   signal present_state, next_state : t_state;
-------------------------------------------------------------------------------

begin -------------------------------------------------------------------------


-- ----------------------------------------------------------------------------
--                             Architecture body
-- ----------------------------------------------------------------------------
  asfifo_low : entity work.ASFIFO_BRAM_XILINX
   generic map(
      DEVICE                  => DEVICE,
      DATA_WIDTH              => DATA_HALF_WIDTH+1,
      ITEMS                   => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET,  --
      ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK_WR         => CLK_WR,
      RST_WR         => RST_WR,
      DI             => data_low,
      WR             => wr_low,
      FULL           => full_l,
      AFULL          => afull_l,

      CLK_RD         => CLK_RD,
      RST_RD         => RST_RD,
      DO             => fifo_out_l,
      RD             => RD,
      EMPTY          => empty_l,
      AEMPTY         => aempty_l
   );

   -------------------------------------------------------------------
     asfifo_high : entity work.ASFIFO_BRAM_XILINX
   generic map(
      DEVICE                  => DEVICE,
      DATA_WIDTH              => DATA_HALF_WIDTH+1,
      ITEMS                   => 512,
      FIRST_WORD_FALL_THROUGH => true,
      DO_REG                  => true,
      ALMOST_FULL_OFFSET      => ALMOST_FULL_OFFSET,  --
      ALMOST_EMPTY_OFFSET     => ALMOST_EMPTY_OFFSET
   )
   port map(
      CLK_WR         => CLK_WR,
      RST_WR         => RST_WR,
      DI             => data_high ,
      WR             => wr_high,
      FULL           => full_h,
      AFULL          => afull_h,

      CLK_RD         => CLK_RD,
      RST_RD         => RST_RD,
      DO             => fifo_out_h,
      RD             => RD,
      EMPTY          => empty_h,
      AEMPTY         => aempty_h
       );
   ----------------------------Data input----------------------------------------
   data_low  (DATA_HALF_WIDTH-1 downto 0)  <= DI;
   data_high (DATA_HALF_WIDTH-1 downto 0)  <= DI;
   --------------------------- Data output-----------------------------------------
      DO_VLD   <= not (empty_l or empty_h);
      DO_VLD_H <= not (fifo_out_l (DATA_HALF_WIDTH) or empty_l);
      DO       <= fifo_out_h(DATA_HALF_WIDTH-1 downto 0) & fifo_out_l(DATA_HALF_WIDTH-1 downto 0);

   ------------------------Control signals-------------------------------------------

     FULL         <= full_h   or full_l;
     AFULL        <= afull_h  or afull_l;
     EMPTY        <= empty_l  or empty_h;
     AEMPTY       <= aempty_l or aempty_h;
     data_low(DATA_HALF_WIDTH)  <= EOP;
     data_high(DATA_HALF_WIDTH) <= EOP;
     --------------------------------------------------------------------
   sync_datamux: process(CLK_WR )
   begin
   if (rising_edge (CLK_WR)) then
      if (RST_WR = '1') then
         present_state <= WRIGHTING_LOW;
      elsif (WR ='1') then
         present_state <= next_state;
      else
         present_state <= WRIGHTING_LOW;
      end if;
   end if ;
   end process;
   ---------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   next_state_logic: process(present_state, EOP)
   begin
      case (present_state) is

      when WRIGHTING_LOW =>
         if (EOP = '1') then
            next_state  <= WRIGHTING_LOW;
         else
            next_state  <= WRIGHTING_HIGH;
         end if ;
      when WRIGHTING_HIGH =>
         next_state  <= WRIGHTING_LOW;
      when others =>
         next_state  <= WRIGHTING_LOW;

      -- - - - - - - - - - - - - - - - - - - - -
      end case;
   end process;

   -- -------------------------------------------------------------------------
   output_logic: process(present_state, WR,EOP)
   begin

      case (present_state) is
      when WRIGHTING_LOW =>

      if (WR ='1'and EOP ='1') then
            wr_high  <= '1';
            wr_low   <= '1';
      elsif (WR='1') then
            wr_low   <= '1';
            wr_high  <= '0';
      else
            wr_low   <= '0';
            wr_high  <= '0';
      end if ;

      when WRIGHTING_HIGH =>

      if (WR ='1') then
            wr_high  <= '1';
            wr_low   <= '0';
         else
            wr_low   <= '0';
            wr_high  <= '0';
      end if;
      -- - - - - - - - - - - - - - - - - - - - -
      when others =>
      -- - - - - - - - - - - - - - - - - - - - -
      end case;
   end process;



   end architecture FULL;
