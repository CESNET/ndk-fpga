--
-- cnt_tb.vhd: Testbench of generic shift register with reset
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
--
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_textio.all;
use ieee.numeric_std.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is
signal clk     : std_logic;
signal reset   : std_logic;
signal din   : std_logic;
signal ce      : std_logic;
signal dout : std_logic;

begin

uut_sh_reg_res : entity work.sh_reg_res
generic map(
   NUM_BITS => 16,
   INIT   => X"5555",
   INIT_EXT00 => X"0000000000000000"
)
port map(
   RESET => reset,
   CLK   => clk,
   DIN    => din,
   CE    => ce,
   DOUT  => dout
);

clk_p : process
begin
   clk <= '1';
   wait for 4 ns;
   clk <= '0';
   wait for 4 ns;
end process;

-- main testbench process
tb : process
begin
   reset <= '1';
   din <= '1';
   ce <= '1';
   wait for 130 ns;
   reset <= '0';
   wait for 700 ns;

end process;

end architecture behavioral;
