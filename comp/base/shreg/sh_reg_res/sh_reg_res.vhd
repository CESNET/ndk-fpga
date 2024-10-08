--
-- sh_reg_res.vhd: Shift Register With Reset
-- Copyright (C) 2006 CESNET
-- Author(s): Michal Spacek <xspace14@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;


-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity sh_reg_res is
   generic(
      DATA_WIDTH  : integer := 1;
      NUM_BITS    : integer := 16;
      INIT_TYPE   : integer := 1; -- recomanded "0"
      INIT        : std_logic_vector := X"00000000000000000000";
      IS_CLK_INVERTED : bit := '0'
   );
   port(
      CLK      : in  std_logic;
      RESET    : in  std_logic;
      CE       : in  std_logic;
      DIN      : in  std_logic_vector(DATA_WIDTH -1 downto 0);
      DOUT     : out std_logic_vector(DATA_WIDTH -1 downto 0)
   );
end entity sh_reg_res;
-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of sh_reg_res is

-- ------------------ Signals declaration -------------------------------------
   signal r_din : std_logic_vector(DATA_WIDTH -1 downto 0);
   signal r_ce  : std_logic;

begin

    r_ce <= RESET or CE;

    r_din <= DIN             when RESET='0' else
             (others => '0') when RESET='1';


SH_REG_U : entity work.sh_reg_base_static
      generic map(
         DATA_WIDTH => DATA_WIDTH,
         NUM_BITS   => NUM_BITS,
         INIT_TYPE  => INIT_TYPE,
         INIT       => INIT,
         IS_CLK_INVERTED => IS_CLK_INVERTED
      )
      port map(
         CLK      => CLK,
         CE       => r_ce,
         DIN      => r_din,
         DOUT     => DOUT
      );



end architecture behavioral;

