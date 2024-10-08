
-- first_one_detector.vhd: This component finds the first 'one' in the std_logic_vector
-- Copyright (C) 2006 CESNET, Liberouter project
-- Author(s): Jan Pazdera <pazdera@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO: -

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;
use std.textio.all;

-- pragma translate_off
library unisim;
use unisim.vcomponents.ALL;
-- pragma translate_on
use work.math_pack.all;

-- -------------------------------------------------------------
--       Entity :
-- -------------------------------------------------------------

entity first_one_detector is
   generic (
      DATA_WIDTH  : integer := 2
   );
   port (
      -- ======
      -- Input
      -- ======

      MASK     : in std_logic_vector(DATA_WIDTH-1 downto 0);

      -- ======
      -- Output
      -- ======

      -- Position of the first 'one' in ONEHOT coding
      FIRST_ONE_ONEHOT  : out std_logic_vector(DATA_WIDTH-1 downto 0);
      -- Position of the first 'one' in BINARY coding
      FIRST_ONE_BINARY  : out std_logic_vector(max(log2(DATA_WIDTH)-1, 0) downto 0);
      -- Deasserted if no 'one' is present in input MASK
      FIRST_ONE_PRESENT : out std_logic
   );
end first_one_detector;

-- -------------------------------------------------------------
--       Architecture :
-- -------------------------------------------------------------
architecture behavioral of first_one_detector is

type t_or_input is array (max(log2(DATA_WIDTH)-1, 0) downto 0) of std_logic_vector(DATA_WIDTH/2 downto 0);
type t_or_output is array (max(log2(DATA_WIDTH)-1, 0) downto 0) of std_logic_vector((DATA_WIDTH/2) downto 0);

signal qtr_first_one    : std_logic_vector(((DATA_WIDTH-2)/3)+1 downto 0);
signal first_one_i      : std_logic_vector(DATA_WIDTH-1 downto 0);
signal first_one_b      : std_logic_vector(max(log2(DATA_WIDTH)-1, 0) downto 0);
signal first_one_or_input  : t_or_input;
signal first_one_or_output : t_or_output;

begin

width_one_gen: if (DATA_WIDTH = 1) generate
   first_one_i(0) <= MASK(0);
   first_one_b(0) <= '0';
   qtr_first_one(((DATA_WIDTH-2)/3)+1) <= MASK(0);
end generate;

width_greater_one_gen: if (DATA_WIDTH > 1) generate
   -- -------------------------------------------------------------
   -- qtr_first_one signal generation

   qtr_first_one(0) <= MASK(0);

   zero_module_gen: if ((DATA_WIDTH-1) mod 3 = 0) generate
         qtr_first_one_gen: for i in 0 to ((DATA_WIDTH-2)/3) generate
            qtr_first_one(i+1) <= qtr_first_one(i) or MASK((3*i) + 1) or MASK((3*i) + 2) or MASK((3*i) + 3);
         end generate;
   end generate;

   one_module_gen: if ((DATA_WIDTH-1) mod 3 = 1) generate
         qtr_first_one_gen: for i in 0 to ((DATA_WIDTH-2)/3) generate
            non_last_i_gen: if (i < ((DATA_WIDTH-2)/3)) generate
               qtr_first_one(i+1) <= qtr_first_one(i) or MASK((3*i) + 1) or MASK((3*i) + 2) or MASK((3*i) + 3);
            end generate;
            last_i_gen: if (i = ((DATA_WIDTH-2)/3)) generate
               qtr_first_one(i+1) <= qtr_first_one(i) or MASK((3*i) + 1);
            end generate;
         end generate;
   end generate;

   two_module_gen: if ((DATA_WIDTH-1) mod 3 = 2) generate
         qtr_first_one_gen: for i in 0 to ((DATA_WIDTH-2)/3) generate
            non_last_i_gen: if (i < ((DATA_WIDTH-2)/3)) generate
               qtr_first_one(i+1) <= qtr_first_one(i) or MASK((3*i) + 1) or MASK((3*i) + 2) or MASK((3*i) + 3);
            end generate;
            last_i_gen: if (i = ((DATA_WIDTH-2)/3)) generate
               qtr_first_one(i+1) <= qtr_first_one(i) or MASK((3*i) + 1) or MASK((3*i) + 2);
            end generate;
         end generate;
   end generate;

   -- -------------------------------------------------------------
   -- first_one_i signal generation
   first_one_i(0) <= MASK(0);

   first_one_i_gen: for i in 1 to (DATA_WIDTH - 1) generate
         zero_module_gen: if ((i-1) mod 3 = 0) generate
            first_one_i(i) <= (not qtr_first_one((i-1)/3)) and MASK(i);
         end generate;
         one_module_gen: if ((i-1) mod 3 = 1) generate
            first_one_i(i) <= (not qtr_first_one((i-1)/3)) and (not first_one_i(i-1)) and MASK(i);
         end generate;
         two_module_gen: if ((i-1) mod 3 = 2) generate
            first_one_i(i) <= (not qtr_first_one((i-1)/3)) and (not first_one_i(i-1)) and (not first_one_i(i-2)) and MASK(i);
         end generate;
   end generate;

   -- Encoder providing correct translation from ONEHOT to BINARY encoding
   encoder_i : entity work.GEN_ENC
   generic map (
      ITEMS => DATA_WIDTH
   )
   port map (
      DI    => first_one_i,
      ADDR  => first_one_b
   );

end generate;

-- -------------------------------------------------------------
-- Output mapping

FIRST_ONE_ONEHOT  <= first_one_i;
FIRST_ONE_BINARY  <= first_one_b;
FIRST_ONE_PRESENT <= qtr_first_one(((DATA_WIDTH-2)/3)+1);

end behavioral;



