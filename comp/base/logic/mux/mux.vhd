-- mux.vhd: Generic multiplexer
-- Copyright (C) 2006 CESNET
-- Author(s): Martin Kosek <kosek@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
entity GEN_MUX is
   generic(
      DATA_WIDTH  : integer := 64;
      MUX_WIDTH   : integer := 15   -- multiplexer width (number of inputs)
   );
   port(
      DATA_IN     : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
      SEL         : in  std_logic_vector(max(1,log2(MUX_WIDTH))-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity GEN_MUX;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of GEN_MUX is
   constant MUX_WIDTH_EXT : integer := 2**max(log2(MUX_WIDTH),1);

   signal slv_array_data_in : slv_array_t(0 to MUX_WIDTH-1)(DATA_WIDTH-1 downto 0);
   signal slv_array_data_in_ext : slv_array_t(0 to MUX_WIDTH_EXT-1)(DATA_WIDTH-1 downto 0) :=
          (others => (others => 'X'));
begin

   slv_array_data_in <= slv_array_to_deser(DATA_IN, MUX_WIDTH, DATA_WIDTH);
   slv_array_data_in_extg: for i in 0 to MUX_WIDTH-1 generate
      slv_array_data_in_ext(i) <= slv_array_data_in(i);
   end generate;

   gen_muxg: if MUX_WIDTH /= 1 generate
      DATA_OUT <= slv_array_data_in_ext(to_integer(unsigned(SEL)));
   end generate;

   fake_gen_muxg: if MUX_WIDTH = 1 generate
      DATA_OUT <= slv_array_data_in_ext(0);
   end generate;
end architecture full;

