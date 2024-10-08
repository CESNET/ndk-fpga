--
-- testbench.vhd: Testbench of top level entity
-- Copyright (C) 2008 CESNET
-- Author(s): Vozenilek Jan <xvozen00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
--
-- TODO:
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity testbench is
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of testbench is

  constant TEST_WIDTH : integer := 64;
  constant TEST_FLOWS : integer := 2;
  constant TEST_BLK_S : integer := 8;
  constant LUT_MEM    : boolean := false;
  constant OUTREG     : boolean := false;
  constant GLOB_STATE : boolean := true;
  constant clkper     : time    := 10 ns;
  constant TEST_FL_W  : integer := TEST_WIDTH/TEST_FLOWS;

  signal clk        : std_logic;
  signal reset      : std_logic;

  signal wr         : std_logic_vector(TEST_FLOWS-1 downto 0);
  signal di         : std_logic_vector(TEST_WIDTH-1 downto 0);

  signal rd         : std_logic;
  signal blk_addr   : std_logic_vector(abs(log2(TEST_FLOWS)-1) downto 0);
  signal rd_addr    : std_logic_vector(log2(TEST_BLK_S)-1 downto 0);
  signal rel_length : std_logic_vector(log2(TEST_BLK_S+1)*TEST_FLOWS-1 downto 0);
  signal rel_dv     : std_logic_vector(TEST_FLOWS-1 downto 0);
  signal do         : std_logic_vector(TEST_WIDTH-1 downto 0);
  signal dv         : std_logic;

  signal empty      : std_logic_vector(TEST_FLOWS-1 downto 0);
  signal full       : std_logic_vector(TEST_FLOWS-1 downto 0);
  signal status     : std_logic_vector(log2(TEST_BLK_S+1)*TEST_FLOWS-1 downto 0);

-- ----------------------------------------------------------------------------
--                      Architecture body
-- ----------------------------------------------------------------------------
begin

uut : entity work.NFIFO2MEM
generic map(
  DATA_WIDTH => TEST_WIDTH,
  FLOWS      => TEST_FLOWS,
  BLOCK_SIZE => TEST_BLK_S,
  LUT_MEMORY => LUT_MEM,
  OUTPUT_REG => OUTREG,
  GLOB_STATE => GLOB_STATE
)
port map(
  CLK        => clk,
  RESET      => reset,

  -- Write interface
  DATA_IN    => di,
  WRITE      => wr,

  -- Read interface
  DATA_OUT   => do,
  DATA_VLD   => dv,
  BLOCK_ADDR => blk_addr,
  RD_ADDR    => rd_addr,
  READ       => rd,
  REL_LEN    => rel_length,
  REL_LEN_DV => rel_dv,
  PIPE_EN    => '1',

  EMPTY      => empty,
  FULL       => full,
  STATUS     => status
);

-- ----------------------------------------------------
-- CLK clock generator
clkgen : process
begin
   clk <= '1';
   wait for clkper/2;
   clk <= '0';
   wait for clkper/2;
end process;

tb : process
begin

reset    <= '1';
wr       <= (others => '0');
blk_addr <= (others => '0');
rd_addr  <= (others => '0');
rd       <= '0';
rel_length <= (others => '0');
rel_dv   <= (others => '0');
di       <= (others => '0');
wait for clkper*8;
reset    <= '0';
wait for clkper*4;

--wr(0) <= '1';
wr <= (others => '1');
for j in 1 to 20 loop
  for k in 0 to TEST_FLOWS-1 loop
    di(k*TEST_FL_W+TEST_FL_W-1 downto k*TEST_FL_W) <= conv_std_logic_vector(j, TEST_FL_W);
  end loop;
  wait for clkper;
end loop;

di <= (others => '0');
wr <= (others => '0');
wait for 4*clkper;

rd       <= '1';
blk_addr <= (others => '0');

for j in 0 to 20 loop
  wait for clkper;
  blk_addr <= blk_addr+1;
  if (blk_addr = TEST_FLOWS-1) then
    blk_addr <= (others => '0');
  end if;
  if (j mod TEST_FLOWS = TEST_FLOWS-1) then
    rd_addr <= rd_addr + 1;
    if (rd_addr = TEST_BLK_S-1) then
      rd_addr <= (others => '0');
    end if;
  end if;
end loop;
rd <= '0';
wait for clkper*10;

rel_length <= conv_std_logic_vector(8, rel_length'length);
rel_dv(0)  <= '1';
wait for clkper;
rel_dv     <= (others => '0');
wait for 4*clkper;

end process;

-- ----------------------------------------------------------------------------
end architecture behavioral;
