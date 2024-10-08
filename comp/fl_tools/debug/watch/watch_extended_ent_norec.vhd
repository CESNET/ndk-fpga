-- watch_extended_ent_norec.vhd: Frame Link watch comp to gather statistics about trafic with no record inside
-- Copyright (C) 2006 CESNET
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
entity FL_WATCH_EXTENDED_NOREC is
   generic(
      INTERFACES     : integer := 1;  -- At least 1
      CNTR_WIDTH     : integer := 32;
      PIPELINE_LEN   : integer := 1;   -- At least 1
      GUARD          : boolean := true;
      PARTS          : integer := 1
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

      MI_DWR	     : in std_logic_vector(31 downto 0);
      MI_ADDR        : in std_logic_vector(31 downto 0);
      MI_RD	     : in std_logic;
      MI_WR	     : in std_logic;
      MI_BE	     : in std_logic_vector(3 downto 0);
      MI_DRD	     : out std_logic_vector(31 downto 0);
      MI_ARDY	     : out std_logic;
      MI_DRDY	     : out std_logic
   );
end entity FL_WATCH_EXTENDED_NOREC;
