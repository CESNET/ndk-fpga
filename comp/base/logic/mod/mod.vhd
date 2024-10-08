-- mod.vhd
--!
--! \file
--! \brief Generic "modulo constant" block.
--! \author Lukas Kekely <kekely@cesnet.cz>
--! \date 2013
--!
--! \section License
--!
--! Copyright (C) 2013 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
--! Library containing log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------
--! \brief Entity of generic modulo constant block.
entity GEN_MOD is
   generic(
      --! \brief Data width of input value.
      DATA_WIDTH  : integer := 16;
      --! \brief Modulo constant.
      --! \descrition WARNING: Usage with modulos that are not powers of 2 and Vivado can lead to very bad results!
      MODULO      : integer := 3
   );
   port(
      --! \brief Input value.
      VALUE     : in  std_logic_vector(max(1,DATA_WIDTH)-1 downto 0);
      --! \brief Modulo result value (VALUE mod MODULO).
      RESULT    : out std_logic_vector(max(1,log2(MODULO))-1 downto 0)
   );
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
--! \brief Full implementation of generic modulo constant block.
architecture full of GEN_MOD is
  signal res  : std_logic_vector(max(1,log2(MODULO))-1 downto 0) := (others => '0');
begin
  -- Actual modulo is needed
  need_mod_gen : if 2**DATA_WIDTH>MODULO and MODULO>1 generate
    -- Modulo is simple with powers of 2
    cutoff_mod_gen : if 2**log2(MODULO)=MODULO generate
      res <= VALUE(res'length-1 downto 0);
    end generate;
    -- Real modulo constant computing
    real_mod_gen : if 2**log2(MODULO)/=MODULO generate
      -- XST can handle this correctly and optimize it nicely, Vivado cannot!!!
      res <= conv_std_logic_vector(conv_integer(VALUE) mod MODULO,res'length);
    end generate;
  end generate;

  -- No need for modulo
  fake_mod_gen1 : if 2**DATA_WIDTH<=MODULO and MODULO>1 generate
    res(VALUE'length-1 downto 0) <= VALUE;
  end generate;
  fake_mod_gen2 : if 2**DATA_WIDTH>MODULO and MODULO<=1 generate
    res <= "0";
  end generate;
  RESULT <= res;
end architecture full;

