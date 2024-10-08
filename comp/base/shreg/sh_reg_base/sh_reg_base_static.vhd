--
-- sh_reg_static.vhd: generic buss from Shift Register
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
use IEEE.std_logic_arith.all;
use work.math_pack.all;
-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity SH_REG_BASE_STATIC is
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

      -- OPT: If you use small NUM_BITSi(1-4) then VIVADO can change srl16E to flip-flop register.
      -- If you realy want shift register SRL prease use option SRL. REG options allways use flip-flop registers.
      -- VIVADO, SRL, REG
      OPT             : string := "VIVADO";
      DEVICE          : string := "7SERIES"
   );
   port(
      CLK      : in  std_logic;
      CE       : in  std_logic;

      DIN      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      DOUT     : out std_logic_vector(DATA_WIDTH-1 downto 0)
   );

end entity SH_REG_BASE_STATIC;


architecture sh_reg_static_arch of SH_REG_BASE_STATIC is
  attribute keep_hierarchy : string;
  attribute keep_hierarchy of SH_REG_BUS_i : label is "no";
begin

  SH_REG_BUS_i : entity work.sh_reg_base_dynamic
    generic map(
      DATA_WIDTH => DATA_WIDTH,
      NUM_BITS   => NUM_BITS,
      INIT_TYPE  => INIT_TYPE,
      INIT       => INIT,
      IS_CLK_INVERTED => IS_CLK_INVERTED,
      OPT        => OPT,
      DEVICE     => DEVICE
    )
    port map(
      CLK  => CLK,
      CE   => CE,
      ADDR => conv_std_logic_vector(NUM_BITS-1, log2(NUM_BITS)),

      DIN  => DIN,
      DOUT => DOUT
   );


end sh_reg_static_arch;


