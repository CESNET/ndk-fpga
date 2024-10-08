-- fl_watch_2.vhd: Frame Link watch comp to gather statistics about traffic
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
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
entity FL_WATCH_2 is
   port(
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      SOF_N          : in std_logic_vector(1 downto 0);
      EOF_N          : in std_logic_vector(1 downto 0);
      SOP_N          : in std_logic_vector(1 downto 0);
      EOP_N          : in std_logic_vector(1 downto 0);
      DST_RDY_N      : in std_logic_vector(1 downto 0);
      SRC_RDY_N      : in std_logic_vector(1 downto 0);

      FRAME_ERR      : out std_logic_vector(1 downto 0);

      MI_DWR	      : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	         : in std_logic;
      MI_WR	         : in std_logic;
      MI_BE	         : in std_logic_vector(3 downto 0);
      MI_DRD         : out std_logic_vector(31 downto 0);
      MI_ARDY        : out std_logic;
      MI_DRDY        : out std_logic
   );
end entity FL_WATCH_2;

architecture full of fl_watch_2 is
begin

   fl_watch_i : entity work.FL_WATCH_NOREC
   generic map(
      INTERFACES     => 2,  -- At least 1
      CNTR_WIDTH     => 32,
      PIPELINE_LEN   => 2,   -- At least 1
      GUARD          => true,
      HEADER         => false,
      FOOTER         => false
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      SOF_N          => SOF_N,
      EOF_N          => EOF_N,
      SOP_N          => SOP_N,
      EOP_N          => EOP_N,
      DST_RDY_N      => DST_RDY_N,
      SRC_RDY_N      => SRC_RDY_N,

      FRAME_ERR      => FRAME_ERR,

      MI_DWR	      => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD	         => MI_RD,
      MI_WR	         => MI_WR,
      MI_BE	         => MI_BE,
      MI_DRD         => MI_DRD,
      MI_ARDY        => MI_ARDY,
      MI_DRDY        => MI_DRDY
   );

end architecture full;
