-- mux_onehot.vhd: Generic multiplexer with onehot select signal
-- Copyright (C) 2014 CESNET
-- Author(s): Lukas Kekely <kekely@cesnet.cz>
--            Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
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
entity GEN_MUX_ONEHOT is
   generic(
      DATA_WIDTH  : integer := 64;
      MUX_WIDTH   : integer := 64;   -- multiplexer width (number of inputs)
      DEVICE        : string := "none" --! "VIRTEX6", "7SERIES", "ULTRASCALE", "none" (behavioral)
   );
   port(
      DATA_IN     : in  std_logic_vector(DATA_WIDTH*MUX_WIDTH-1 downto 0);
      SEL         : in  std_logic_vector(MUX_WIDTH-1 downto 0);
      DATA_OUT    : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );
end entity GEN_MUX_ONEHOT;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of GEN_MUX_ONEHOT is

   signal sel_bin : std_logic_vector(max(1,log2(MUX_WIDTH))-1 downto 0);

begin

   gen_enci: entity work.GEN_ENC
   generic map(
      ITEMS => MUX_WIDTH,
      DEVICE => DEVICE
   )
   port map(
      DI => SEL,
      ADDR => sel_bin
   );

   gen_muxi: entity work.GEN_MUX
   generic map(
      DATA_WIDTH => DATA_WIDTH,
      MUX_WIDTH => MUX_WIDTH
   )
   port map(
      DATA_IN => DATA_IN,
      SEL => sel_bin,
      DATA_OUT => DATA_OUT
   );

end architecture full;

