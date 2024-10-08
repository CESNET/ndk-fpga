-- watch_lb_norec.vhd: Frame Link watch local bus cover with no record inside
-- Copyright (C) 2006 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--            Lukas Solanka <solanka@liberouter.org>
--            Jan Stourac <xstour03@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

-- library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity FL_WATCH_LB_NOREC is
   generic(
      -- At least 1
      INTERFACES     : integer := 1;
      CNTR_WIDTH     : integer := 32;
      -- At least 1
      PIPELINE_LEN   : integer := 1;
      GUARD          : boolean := true;
      HEADER         : boolean := true;
      FOOTER         : boolean := true;

      -- =========
      -- Local bus
      -- =========

      -- base address
      BASE_ADDR      : integer;
      -- address width
      ADDR_WIDTH     : integer;
      -- frequency
      FREQUENCY      : integer := 100
   );
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOF_N          : in std_logic_vector(INTERFACES-1 downto 0);
      SOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      EOP_N          : in std_logic_vector(INTERFACES-1 downto 0);
      DST_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);
      SRC_RDY_N      : in std_logic_vector(INTERFACES-1 downto 0);

      -- =================
      -- Local bus signals
      -- =================

      LBCLK       : in    std_logic;
       -- Frame
      LBFRAME     : in    std_logic;
      -- Hold Ack (HOLDA), active LOW
      LBHOLDA     : out   std_logic;
      -- Address/Data
      LBAD        : inout std_logic_vector(15 downto 0);
      -- Adress strobe
      LBAS        : in    std_logic;
      LBRW        : in    std_logic;
      -- Ready, active LOW
      LBRDY       : out   std_logic;
      LBLAST      : in    std_logic
   );
end entity FL_WATCH_LB_NOREC;


-- ----------------------------------------------------------------------------
--                               Architecture
-- ----------------------------------------------------------------------------
architecture full of FL_WATCH_LB_NOREC is
   -- MI32 connection
   signal mi_dwr       : std_logic_vector(31 downto 0);
   signal mi_addr      : std_logic_vector(31 downto 0);
   signal mi_rd        : std_logic;
   signal mi_wr	       : std_logic;
   signal mi_be	       : std_logic_vector(3 downto 0);
   signal mi_drd       : std_logic_vector(31 downto 0);
   signal mi_ardy      : std_logic;
   signal mi_drdy      : std_logic;

begin

   FL_WATCH_MI_U: entity work.FL_WATCH_NOREC
      generic map (
         INTERFACES     => INTERFACES,
         CNTR_WIDTH     => CNTR_WIDTH,
         PIPELINE_LEN   => PIPELINE_LEN,
         GUARD          => GUARD,
         HEADER         => HEADER,
         FOOTER         => FOOTER
      )
      port map (
         CLK            => CLK,
         RESET          => RESET,

         SOF_N          => SOF_N,
         EOF_N          => EOF_N,
         SOP_N          => SOP_N,
         EOP_N          => EOP_N,
         DST_RDY_N      => DST_RDY_N,
         SRC_RDY_N      => SRC_RDY_N,

         MI_DWR         => mi_dwr,
	 MI_ADDR        => mi_addr,
	 MI_RD	        => mi_rd,
	 MI_WR	        => mi_wr,
	 MI_BE	        => mi_be,
	 MI_DRD	        => mi_drd,
	 MI_ARDY        => mi_ardy,
	 MI_DRDY        => mi_drdy
      );

   mi_addr(31 downto ADDR_WIDTH) <= (others => '0');
   mi_be <= (others => '1');

   LB_CONNECT_U: entity work.lb_connect
      generic map (
         BASE_ADDR  => BASE_ADDR,
         ADDR_WIDTH => ADDR_WIDTH,
         FREQUENCY  => FREQUENCY
      )
      port map (
         -- Control signals
         RESET             => RESET,

         -- LB signals
         LBCLK       => LBCLK,
         LBFRAME     => LBFRAME,
         LBHOLDA     => LBHOLDA,
         LBAD        => LBAD,
         LBAS        => LBAS,
         LBRW        => LBRW,
         LBRDY       => LBRDY,
         LBLAST      => LBLAST,

         -- Address decoder interface
         CLK         => CLK,
         ADC_RD      => mi_rd,
         ADC_WR      => mi_wr,
         ADC_ADDR    => mi_addr(ADDR_WIDTH - 1 downto 0),
         ADC_DI      => mi_dwr,
         ADC_DO      => mi_drd,
         ADC_DRDY    => mi_drdy
      );

end architecture full;


