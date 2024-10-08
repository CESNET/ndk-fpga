-- cam_fill_element.vhd: Basic filling element of CAM.
-- Copyright (C) 2005 CESNET
-- Author(s): Martin kosek <xkosek00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity cam_fill_element is
   generic(
      -- Width of internal storage element
      -- 4 for VirtexII SRL16E (legacy, but works also for V5,6,7)
      -- 5 for Virtex5,6,7 SRLC32E
      -- 6 for Virtex5,6,7 RAM64x1S (stores 6 bits/LUT, most effective)
      ELEM_WIDTH        : integer := 4;
      -- If true, writing a masked bit (mask=0) has two different meanings:
      --    If the bit is 0, then it is don't care
      --    But if the bit is 1, then it is UNMATCHABLE!
      USE_UNMATCHABLE   : boolean := false
   );
   port(
      CNT_IN         : in std_logic_vector(ELEM_WIDTH-1 downto 0);
      MASK_IN        : in std_logic_vector(ELEM_WIDTH-1 downto 0);
      DATA_IN        : in std_logic_vector(ELEM_WIDTH-1 downto 0);
      DATA_FILL      : out std_logic
   );
end entity cam_fill_element;


-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture cam_fill_element_arch of cam_fill_element is

-- ------------------ Signals declaration -------------------------------------
   signal and1_out : std_logic_vector(ELEM_WIDTH-1 downto 0);
   signal and2_out : std_logic_vector(ELEM_WIDTH-1 downto 0);

begin

NO_UNM_GEN : if USE_UNMATCHABLE = false generate
   and1_out <= CNT_IN and MASK_IN;
   and2_out <= DATA_IN and MASK_IN;
end generate;

UNM_GEN : if USE_UNMATCHABLE = true generate
   and1_out <= CNT_IN and MASK_IN;
   and2_out <= DATA_IN;
end generate;

DATA_FILL <= '1' when (and1_out = and2_out) else '0';

end architecture cam_fill_element_arch;
