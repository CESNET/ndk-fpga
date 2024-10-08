--
-- testbench.vhd: Testbench for MI_Splitter
-- Copyright (C) 2006 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.conv_std_logic_vector;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

use work.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            ENTITY DECLARATION                             --
-- ----------------------------------------------------------------------------

entity testbench is
end testbench;

-- ----------------------------------------------------------------------------
--                         ARCHITECTURE DECLARATION                          --
-- ----------------------------------------------------------------------------

architecture behavior of testbench is

   -- Simulation constants ----------------------------------------------------
   constant clk_per      : time    := 10 ns;
   constant ITEMS        : integer := 3;
   constant DATA_WIDTH   : integer := 16;
   constant ADDR_WIDTH   : integer := 4;
   constant PIPE         : boolean := false;

   constant LATENCY      : integer := 1; -- mem latency simulation(0 or 1 or >2)
   constant ARDY_DELAY_CONST : integer := 0; -- delay of ARDY signal (0 or >1)

   -- clock & reset & sync ----------------------------------------------------
   signal clk         : std_logic;
   signal reset       : std_logic;

   -- Input MI interface ---------------------------------------------------
   signal in_dwr      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_addr     : std_logic_vector((ADDR_WIDTH+log2(ITEMS))-1 downto 0);
   signal in_be       : std_logic_vector(DATA_WIDTH/8-1 downto 0);
   signal in_rd       : std_logic;
   signal in_wr       : std_logic;
   signal in_ardy     : std_logic;
   signal in_drd      : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal in_drdy     : std_logic;

   -- Output MI interfaces -------------------------------------------------
   signal out_dwr     : std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
   signal out_addr    : std_logic_vector(ITEMS*ADDR_WIDTH-1 downto 0);
   signal out_be      : std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
   signal out_rd      : std_logic_vector(ITEMS-1 downto 0);
   signal out_wr      : std_logic_vector(ITEMS-1 downto 0);
   signal out_ardy    : std_logic_vector(ITEMS-1 downto 0);
   signal out_drd     : std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
   signal out_drdy    : std_logic_vector(ITEMS-1 downto 0);

   -------------------------------------------------------------------------

   type t_drd_delay  is array(0 to LATENCY-3) of
                                 std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
   type t_drdy_delay is array(0 to LATENCY-3) of
                                 std_logic_vector(ITEMS-1 downto 0);
   type t_ardy_delay is array(0 to ARDY_DELAY_CONST-2) of
                                 std_logic_vector(ITEMS-1 downto 0);

   signal drd_delay       : t_drd_delay;
   signal drdy_delay      : t_drdy_delay;
   signal drd_delay_in    : std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
   signal drd_delay_out   : std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
   signal drdy_delay_in   : std_logic_vector(ITEMS-1 downto 0);
   signal drdy_delay_out  : std_logic_vector(ITEMS-1 downto 0);

   signal ardy_delay      : t_ardy_delay;
   signal ardy_delay_in   : std_logic_vector(ITEMS-1 downto 0);
   signal ardy_delay_out  : std_logic_vector(ITEMS-1 downto 0);

   signal out_rd_delayed  : std_logic_vector(ITEMS-1 downto 0);
   signal out_wr_delayed  : std_logic_vector(ITEMS-1 downto 0);

begin

   -- -------------------------------------------------------------------------
   --                      MI Splitter component mapping                     --
   -- -------------------------------------------------------------------------

   UUT : entity work.MI_SPLITTER
   generic map(
      ITEMS          => ITEMS,
      DATA_WIDTH     => DATA_WIDTH,
      ADDR_WIDTH     => ADDR_WIDTH,
      PIPE           => PIPE
   )
   port map(
      CLK            => clk,
      RESET          => reset,

      IN_DWR         => in_dwr,
      IN_ADDR        => in_addr,
      IN_RD          => in_rd,
      IN_WR          => in_wr,
      IN_ARDY        => in_ardy,
      IN_BE          => in_be,
      IN_DRD         => in_drd,
      IN_DRDY        => in_drdy,

      OUT_DWR        => out_dwr,
      OUT_ADDR       => out_addr,
      OUT_RD         => out_rd,
      OUT_WR         => out_wr,
      OUT_ARDY       => out_ardy,
      OUT_BE         => out_be,
      OUT_DRD        => out_drd,
      OUT_DRDY       => out_drdy

   );

   -- -------------------------------------------------------------------------
   --                        Memory components mapping                       --
   -- -------------------------------------------------------------------------

   MEMORY : for i in 0 to ITEMS-1 generate

      LAT_NOT_0 : if (LATENCY /= 0) generate
      --LAT_NOT_0 : if (i mod 2 = 0) generate
         MEM : entity work.SP_BMEM
         generic map(
            DATA_WIDTH     => DATA_WIDTH,
            ITEMS          => 2**ADDR_WIDTH,
            OUTPUT_REG     => FALSE
         )
         port map(
            RESET          => reset,
            CLK            => clk,

            PIPE_EN        => '1',
            RE             => out_rd_delayed(i),
            WE             => out_wr_delayed(i),
            ADDR           => out_addr((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH),
            DI             => out_dwr((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            DO_DV          => drdy_delay_in(i),
            DO             => drd_delay_in((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
         );
         ardy_delay_in(i) <= out_rd(i) or out_wr(i);
      end generate;

      LAT_0 : if (LATENCY = 0) generate
      --LAT_0 : if (i mod 2 = 1) generate
         MEM : entity work.SP_DISTMEM
         generic map(
            DATA_WIDTH     => DATA_WIDTH,
            ITEMS          => 2**ADDR_WIDTH
         )
         port map(
            DI             => out_dwr((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH),
            WE             => out_wr_delayed(i),
            WCLK           => clk,
            ADDR           => out_addr((i+1)*ADDR_WIDTH-1 downto i*ADDR_WIDTH),
            DO             => drd_delay_in((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH)
         );
         ardy_delay_in(i) <= out_rd(i) or out_wr(i);
         drdy_delay_in(i) <= out_rd_delayed(i);
      end generate;

      out_rd_delayed(i) <= out_rd(i) and ardy_delay_out(i);
      out_wr_delayed(i) <= out_wr(i) and ardy_delay_out(i);

   end generate;


   -- -------------------------------------------------------------------------
   --                      Latency of memory simulation                      --
   -- -------------------------------------------------------------------------

   DELAY_IF : if (LATENCY > 2) generate

      delay_p : process(clk)
      begin
         if (clk'event and clk = '1') then
            drd_delay_out  <= drd_delay(0);
            drdy_delay_out <= drdy_delay(0);
            for i in 0 to LATENCY-4 loop
               drd_delay(i)  <= drd_delay(i+1);
               drdy_delay(i) <= drdy_delay(i+1);
            end loop;
            drd_delay(LATENCY-3)  <= drd_delay_in;
            drdy_delay(LATENCY-3) <= drdy_delay_in;
         end if;
         if (reset = '1') then
            for i in 0 to LATENCY-3 loop
               drdy_delay(i) <= (others => '0');
            end loop;
         end if;
      end process;

   end generate;

   DELAY_IF2 : if (LATENCY = 1 or LATENCY = 0) generate

      drd_delay_out  <= drd_delay_in;
      drdy_delay_out <= drdy_delay_in;

   end generate;

--    DELAY_IF3 : if (LATENCY = 0) generate
--
--       drd_delay_out  <= (others => '1');
--       drdy_delay_out <= (others => '1') when (IN_RD = '1') else (others => '0');
--
--    end generate;

   out_drd  <= drd_delay_out;
   out_drdy <= drdy_delay_out;

   -- -------------------------------------------------------------------------
   --                               ARDY delay                               --
   -- -------------------------------------------------------------------------

   ARDY_DELAY_IF : if (ARDY_DELAY_CONST > 1) generate

      delay_p : process(clk)
      begin
         if (clk'event and clk = '1') then
            ardy_delay_out  <= ardy_delay(0);
            for i in 0 to ARDY_DELAY_CONST-3 loop
               ardy_delay(i)  <= ardy_delay(i+1);
            end loop;
            ardy_delay(ARDY_DELAY_CONST-2) <= ardy_delay_in;
         end if;
         if (reset = '1') then
            for i in 0 to ARDY_DELAY_CONST-2 loop
               ardy_delay(i) <= (others => '0');
            end loop;
         end if;
      end process;

   end generate;

   ARDY_DELAY_IF2 : if (ARDY_DELAY_CONST = 0) generate

      ardy_delay_out <= ardy_delay_in;

   end generate;

   out_ardy <= ardy_delay_out;

   -- -------------------------------------------------------------------------
   --                    'Generation of input clock' Process                 --
   -- -------------------------------------------------------------------------

   clk_perp : process
   begin
      clk <= '1';
      wait for clk_per/2;
      clk <= '0';
      wait for clk_per/2;
   end process clk_perp;

   -- -------------------------------------------------------------------------
   --                       'Reset Generation' Process                       --
   -- -------------------------------------------------------------------------

   resetp : process
   begin
      reset<='1';
      wait for 10*clk_per;
      reset<='0';
      wait;
   end process resetp;

-- ----------------------------------------------------------------------------
--                          Main Testbench Process
-- ----------------------------------------------------------------------------


   tb: process

   constant MAXADDR : integer := 2**(log2(ITEMS));

   -- ----------------------------------------------------------------
   --                        Testbench Body
   -- ----------------------------------------------------------------
   begin

      in_addr  <= (others => '0');
      in_dwr   <= (others => '0');
      in_be    <= (others => '0');
      in_rd    <= '0';
      in_wr    <= '0';

      wait until reset'event and reset = '0';
      wait for 3*clk_per;
      wait until clk'event and clk = '1';

      -----------------------------------------------------------------------

      -- writes to all memories to first 10 adresses
      WRITE : for i in 0 to 9 loop

         WRITE_MEMS : for j in 0 to MAXADDR-1 loop

            in_addr  <= (conv_std_logic_vector(j, LOG2(ITEMS)) &
                         conv_std_logic_vector(i, ADDR_WIDTH));
            in_dwr   <= (conv_std_logic_vector(j, DATA_WIDTH/2) &
                         conv_std_logic_vector(i, DATA_WIDTH/2));
            in_be    <= (others => '1');
            in_wr    <= '1';

            wait until clk'event and clk = '1';

            ARDY_WAIT : while (in_ardy = '0') loop
               wait until clk'event and clk = '1';
            end loop;

            in_wr <= '0';

            -- sometimes wait for few clk cykles (1 to 3)
            if (i mod 2 = 1) then
               for k in 0 to (((i+j) mod 3 )-1) loop
                  wait until clk'event and clk = '1';
               end loop;
            end if;

         end loop;

      end loop;

      wait for 20*clk_per;

      ----------------------------------------------------------------------

      -- reads from all memories from first 10 adresses
      READ : for i in 0 to 9 loop

         READ_MEMS : for j in 0 to MAXADDR-1 loop

            in_addr  <= (conv_std_logic_vector(j, LOG2(ITEMS)) &
                         conv_std_logic_vector(i, ADDR_WIDTH));
            in_rd    <= '1';

            wait until clk'event and clk = '1';

            ARDY_WAIT2 : while (in_ardy = '0') loop
               wait until clk'event and clk = '1';
            end loop;
            in_rd <= '0';

            -- sometimes wait for few clk cykles (1 to 3)
            --if (i mod 2 = 1) then
               for k in 0 to (((i+j) mod 3 )-1) loop
                  wait until clk'event and clk = '1';
               end loop;
            --end if;

         end loop;

      end loop;

      wait for 20*clk_per;

      -- ----------------------------------------------------------------------

      -- reads some adresses from one memory and then from the other
      READ_MEMS2 : for j in 0 to MAXADDR-1 loop

         READ2 : for i in 0 to 9 loop

            in_addr  <= (conv_std_logic_vector(j, LOG2(ITEMS)) &
                         conv_std_logic_vector(i, ADDR_WIDTH));
            in_rd    <= '1';

            wait until clk'event and clk = '1';

            ARDY_WAIT3 : while (in_ardy = '0') loop
               wait until clk'event and clk = '1';
            end loop;
            in_rd <= '0';

            -- sometimes wait for few clk cykles (1 to 3)
            --if (i mod 2 = 1) then
               for k in 0 to (((i+j) mod 3 )-1) loop
                  wait until clk'event and clk = '1';
               end loop;
            --end if;

         end loop;

         wait for 4*clk_per;

      end loop;

      -- ----------------------------------------------------------------------
      -- ----------------------------------------------------------------------
      wait;
   end process;

end;



