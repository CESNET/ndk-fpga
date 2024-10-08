--
-- sh_reg_base_dynamic_ent.vhd: generic buss from Shift Register
-- Copyright (C) 2015 CESNET
-- Author(s): Radek Isa <xisara00@stud.fit.vutbr.cz>
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
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SH_REG_BASE_DYNAMIC is
   generic(
      --bus size
      DATA_WIDTH      : integer := 1;
      -- number of bits save in srl register
      NUM_BITS        : integer := 16;

      -- 0 => all data is "0", 1 => same columns (all collumns are inicialization to same value),
      -- 2 => same lines (all lines are inicialization to same value), 3 => init all data
      INIT_TYPE       : integer := 0;
      -- Data is truncated from right (INIT => "842000" for 4 bits INIT => "8420" )
      INIT            : std_logic_vector := x"000000000000000000000000";
      -- change activation edge  0 => (CLK'event and CLK = 1), 1 => (CLK'event and CLK=0)
      IS_CLK_INVERTED : bit     := '0';

      -- Optimalization: If you use small NUM_BITS (1-4) then VIVADO can change srl16E to flip-flop register. It cost more resources.
      -- If you realy want shift register SRL prease use option SRL. Option REG use allways flip-flop registers
      -- VIVADO, SRL, REG
      OPT             : string := "VIVADO";

      DEVICE          : string := "7SERIES"
   );
   port(
      CLK      : in  std_logic;
      CE       : in  std_logic;
      ADDR     : in  std_logic_vector(log2(NUM_BITS) -1 downto 0);

      DIN      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DOUT     : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );

end entity SH_REG_BASE_DYNAMIC;




