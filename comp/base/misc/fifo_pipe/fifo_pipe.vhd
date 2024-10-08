-- fifo_pipe.vhd : FIFO PIPE entity and architecture
--!
--! \file
--! \brief FIFO PIPE entity and architecture
--! \author Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--! \date 2018
--!
--! \section License
--!
--! Copyright (C) 2018 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!


library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;
use work.math_pack.all;


--! -----------------------------------------------------------------------------
--!                            Entity declaration
--! -----------------------------------------------------------------------------

entity fifo_pipe is
generic (
   -- transafer data width
   DATA_WIDTH        : integer := 64;
   -- pipeline levels before FIFO
   PIPE_N            : integer := 4;
   -- FIFO output register
   OUT_REG           : boolean := false
);
port (

   -- -------------------------------------------------------------------------
   -- Clock & Reset
   -- -------------------------------------------------------------------------

   CLK               : in  std_logic;
   RESET             : in  std_logic;

   -- -------------------------------------------------------------------------
   -- RX interface
   -- -------------------------------------------------------------------------

   -- source ready
   RX_SRC_RDY        : in  std_logic;
   -- destination ready
   RX_DST_RDY        : out std_logic;

   -- data
   RX_DATA           : in  std_logic_vector(DATA_WIDTH-1 downto 0);

   -- -------------------------------------------------------------------------
   -- TX interface
   -- -------------------------------------------------------------------------

   -- source ready
   TX_SRC_RDY        : out std_logic;
   -- destination ready
   TX_DST_RDY        : in  std_logic;

   -- data
   TX_DATA           : out std_logic_vector(DATA_WIDTH-1 downto 0)

);
end entity fifo_pipe;

architecture full of fifo_pipe is

   -- -------------------------------------------------------------------------

   constant FIFO_SIZE        : integer := PIPE_N*4+2;
   constant FIFO_AFULL_LIMIT : integer := PIPE_N*2+2;

   constant SMALL_FIFO_MAX   : integer := 31;

   -- -------------------------------------------------------------------------

   -- pipeline
   signal data_pipeline    : std_logic_vector(PIPE_N*(DATA_WIDTH+1)-1 downto 0);
   signal afull_pipeline   : std_logic_vector(PIPE_N-1 downto 0);

   -- FIFO fill
   signal fifo_fill        : unsigned(log2(FIFO_SIZE+1)-1 downto 0);
   signal fifo_almost_full : std_logic;
   signal fifo_empty       : std_logic;

   -- reset counter
   signal reset_cnt : std_logic_vector(PIPE_N-1 downto 0);

   -- -------------------------------------------------------------------------

begin

   -- -------------------------------------------------------------------------
   -- pipeline
   -- -------------------------------------------------------------------------

   pipeline_gen : process (CLK)
   begin
      if (CLK'event and CLK='1') then
         -- data pipeline
         data_pipeline(PIPE_N*(DATA_WIDTH+1)-1 downto (PIPE_N-1)*(DATA_WIDTH+1)+1) <= RX_DATA;
         data_pipeline((PIPE_N-1)*(DATA_WIDTH+1))                                  <= '1' when RX_SRC_RDY='1' and afull_pipeline(PIPE_N-1)='0' else '0';

         for i in PIPE_N-1-1 downto 0 loop
            data_pipeline((i+1)*(DATA_WIDTH+1)-1 downto i*(DATA_WIDTH+1)) <= data_pipeline((i+1+1)*(DATA_WIDTH+1)-1 downto (i+1)*(DATA_WIDTH+1));
         end loop;

         -- alfull pipeline
         afull_pipeline(0) <= fifo_almost_full;

         for i in 1 to PIPE_N-1 loop
            afull_pipeline(i) <= afull_pipeline(i-1);
         end loop;
      end if;
   end process;

   RX_DST_RDY <= not afull_pipeline(PIPE_N-1);

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- reset counter
   -- -------------------------------------------------------------------------

   reset_cnt_gen : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         reset_cnt(PIPE_N-1) <= '0';
         for i in PIPE_N-1-1 downto 0 loop
            reset_cnt(i) <= reset_cnt(i+1);
         end loop;

         if (RESET='1') then
            reset_cnt <= (others => '1');
         end if;
      end if;
   end process;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- FIFO fill
   -- -------------------------------------------------------------------------

   fifo_fill_gen : process (RESET,CLK)
   begin
      if (CLK'event and CLK='1') then
         if    (data_pipeline(0)='1' and (TX_DST_RDY='0' or  fifo_empty='1')) then -- writing, not reading
            fifo_fill <= fifo_fill+1;
         elsif (data_pipeline(0)='0' and (TX_DST_RDY='1' and fifo_empty='0')) then -- reading, not writing
            fifo_fill <= fifo_fill-1;
         end if;

         if (RESET='1') then
            fifo_fill <= (others => '0');
         end if;
      end if;
   end process;

   fifo_almost_full <= '1' when fifo_fill>=FIFO_AFULL_LIMIT else '0';
   fifo_empty       <= (nor fifo_fill);

   TX_SRC_RDY       <= not fifo_empty;

   -- -------------------------------------------------------------------------

   -- -------------------------------------------------------------------------
   -- output FIFO
   -- -------------------------------------------------------------------------

   small_fifo_gen : if FIFO_SIZE<=SMALL_FIFO_MAX generate
      sh_fifo_gen : entity work.sh_fifo
      generic map (
         FIFO_WIDTH     => DATA_WIDTH,
         FIFO_DEPTH     => FIFO_SIZE,
         USE_INREG      => false,
         USE_OUTREG     => OUT_REG
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         DIN            => data_pipeline(DATA_WIDTH+1-1 downto 0+1),
         WE             => data_pipeline(0) and not reset_cnt(0),

         DOUT           => TX_DATA,
         RE             => TX_DST_RDY and not fifo_empty,

         EMPTY          => open,
         STATUS         => open,
         FULL           => open
      );
   end generate;

   big_fifo_gen : if FIFO_SIZE>SMALL_FIFO_MAX generate
      fifo_gen : entity work.fifo
      generic map (
         DATA_WIDTH     => DATA_WIDTH,
         ITEMS          => FIFO_SIZE,
         DO_REG         => OUT_REG
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         DATA_IN        => data_pipeline(DATA_WIDTH+1-1 downto 0+1),
         WRITE_REQ      => data_pipeline(0) and not reset_cnt(0),

         DATA_OUT       => TX_DATA,
         READ_REQ       => TX_DST_RDY and not fifo_empty,

         EMPTY          => open,
         FULL           => open,
         LSTBLK         => open,
         STATUS         => open
      );
   end generate;

   -- -------------------------------------------------------------------------

end full;
