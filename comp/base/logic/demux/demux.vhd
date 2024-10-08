-- demux.vhd: Generic demultiplexer
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
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
entity GEN_DEMUX is
   generic(
      DATA_WIDTH  : integer;
      DEMUX_WIDTH : integer;  -- demultiplexer width (number of outputs)
      DEF_VALUE   : std_logic := '0' -- default value for unselected outputs
   );
   port(
      DATA_IN     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      SEL         : in  std_logic_vector(max(log2(DEMUX_WIDTH), 1)-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH*DEMUX_WIDTH-1 downto 0)
   );
end entity GEN_DEMUX;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of GEN_DEMUX is
begin

   gen_demuxp: process(SEL, DATA_IN)
   begin
      DATA_OUT <= (others => DEF_VALUE);

      for i in 0 to DEMUX_WIDTH-1 loop
         if DEMUX_WIDTH = 1 or (conv_std_logic_vector(i, log2(DEMUX_WIDTH)) = SEL) then
            DATA_OUT((i+1)*DATA_WIDTH-1 downto i*DATA_WIDTH) <= DATA_IN;
         end if;
      end loop;
   end process;

end architecture full;

