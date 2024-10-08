-- testbench.vhd: Testbench for streaming generator
-- # Copyright (C) 2014 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

entity testbench is

end testbench;

architecture behavioral of testbench is
   signal CLK              : std_logic;
   signal RESET            : std_logic;
   signal REG_DATA_OUT     : std_logic_vector(127 downto 0);
   signal REG_DATA_IN      : std_logic_vector(127 downto 0);
   signal REG_WR_OUT       : std_logic_vector(3 downto 0);
   signal REG_RD_OUT       : std_logic_vector(3 downto 0);
   signal REG_WE_IN        : std_logic_vector(3 downto 0);
   signal REG_ARDY_IN      : std_logic_vector(3 downto 0);
   signal MI_DWR           : std_logic_vector(31 downto 0);
   signal MI_ADDR          : std_logic_vector(31 downto 0);
   signal MI_RD            : std_logic;
   signal MI_WR            : std_logic;
   signal MI_BE            : std_logic_vector(3  downto 0);
   signal MI_DRD           : std_logic_vector(31 downto 0);
   signal MI_ARDY          : std_logic;
   signal MI_DRDY          : std_logic;

begin

   uut : entity work.MI_REGISTER_ARRAY(full)
   generic map(
      --! mi pipe
      MI_PIPE => true,
      --! mi data width
      MI_WIDTH => 32,
      --! mi addres width
      MI_ADDR_WIDTH => 32,
      --! addres fisrt register, width -> (MI_ADDR_WIDTH-1 downto 0)
      FIRST_ADDR(32-1 downto 0) => X"00000008",
      --! significant bits of the mi address
      SIGN_BITS_ADDR => 32,
      --! number of registers
      NUM_REGS => 4,
      --! initialization values for registers, width -> (MI_WIDTH*NUM_REGS-1 downto 0)
      INICIAL(4*32-1 downto 0)=> X"00000004000000030000000200000001",

      --! range must be "1 to NUM_REGS"
      GENER_REGS(1 to 4) =>  ( --! registers data width
                              (DATA_WIDTH => 19,                --! nastavujem generiky pre 1. register
                               --! true - inter , false - exter
                               INTER => true,
                               --! support MI read
                               MI_RD_EN => true,
                               --! support MI write
                               MI_WR_EN => true,
                               --! support user write
                               USR_WR_EN => true,
                               --! response to reset
                               RST_EN => false,
                               --! support MI_BE signal
                               BE_EN => true),

                              (DATA_WIDTH => 19,  --! nastavujem generiki pre 2. register
                               INTER => true,
                               MI_RD_EN => true,
                               MI_WR_EN => true,
                               USR_WR_EN => true,
                               RST_EN => true,
                               BE_EN => true),

                              (DATA_WIDTH => 19,  --! nastavujem generiki pre 3. register
                               INTER => true,
                               MI_RD_EN => true,
                               MI_WR_EN => false,
                               USR_WR_EN => false,
                               RST_EN => true,
                               BE_EN => false),

                              (DATA_WIDTH => 19,  --! nastavujem generiki pre 4. register
                               INTER => true,
                               MI_RD_EN => true,
                               MI_WR_EN => false,
                               USR_WR_EN => false,
                               RST_EN => true,
                               BE_EN => true)
                            )
   )
   port map (
      CLK            => CLK,
      RESET          => RESET,
      REG_DATA_OUT   => REG_DATA_OUT,
      REG_DATA_IN    => REG_DATA_IN,
      REG_WR_OUT     => REG_WR_OUT,
      REG_RD_OUT     => REG_RD_OUT,
      REG_WE_IN      => REG_WE_IN,
      REG_ARDY_IN    => REG_ARDY_IN,
      MI_DWR         => MI_DWR,
      MI_ADDR        => MI_ADDR,
      MI_RD          => MI_RD,
      MI_WR          => MI_WR,
      MI_BE          => MI_BE,
      MI_DRD         => MI_DRD,
      MI_ARDY        => MI_ARDY,
      MI_DRDY        => MI_DRDY
   );
   --! Simulating input flow
   input_flow : process
   begin

      wait for 1 ns;

      MI_DWR <= (others => '0');
      MI_ADDR <= (others => '0');
      MI_BE <= "0001";
      MI_RD <= '0';
      MI_WR <= '0';
      REG_DATA_IN <= (others => '0');
      REG_WE_IN <= (others => '0');
      REG_ARDY_IN <= (others => '0');

      wait for 50 ns;

      MI_RD <= '1';
      MI_ADDR <= X"00000008";
      wait for 10 ns;
      MI_ADDR <= X"0000000C";
      wait for 20 ns;
      MI_RD <= '0';


      MI_ADDR <= X"00000008";
      MI_DWR <= X"FFFFFFFF";
      MI_WR <= '1';
      wait for 10 ns;
      MI_ADDR <= X"0000000C";
      MI_DWR <= X"BBBBBBBB";
      wait for 10 ns;
      MI_ADDR <= X"00000008";
      MI_DWR <= X"DDDDDDDD";
      wait for 10 ns;

      MI_WR <= '0';

      MI_RD <= '1';
      wait for 10 ns;
      MI_RD <= '0';
      wait for 30 ns;

      REG_DATA_IN <= X"000000000000000000000000AAAAAAAA";
      REG_WE_IN(0) <= '1';
      wait for 10 ns;
      REG_WE_IN(0) <= '0';

      MI_RD <= '1';
      wait for 10 ns;
      MI_RD <= '0';

      wait;
   end process input_flow;

   clk_gen_p : process
   begin
      CLK <= '1';
      wait for 5 ns;
      CLK <= '0';
      wait for 5 ns;
   end process clk_gen_p;

   reset_gen : process
   begin
      RESET <= '1';
      wait for 40 ns;
      RESET <= '0';
   wait for 200 ns;
   end process;
end architecture;
