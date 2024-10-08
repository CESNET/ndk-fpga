

library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

library unisim;
use unisim.VCOMPONENTS.all;

entity testbench is
end testbench;

architecture Behavioral of testbench is

signal CLK : std_logic := '0';
signal RESET : std_logic := '1';
signal LED_GREEN, LED_RED : std_logic_vector(2 downto 0);

constant ptrn_0 : std_logic_vector(15 downto 0) := "0001101100011011";
constant ptrn_1 : std_logic_vector(15 downto 0) := "1100110011001100";
constant ptrn_2 : std_logic_vector(15 downto 0) := "1111000110001111";

signal WR_CLK      :  std_logic;
signal RD_CLK      :  std_logic;

signal WR_RESET    :  std_logic;
signal RD_RESET    :  std_logic;

signal WR_ADDR     : std_logic_vector(16-1 downto 0);
signal RD_ADDR     : std_logic_vector(16-1 downto 0);


signal RX_MVB_DATA : std_logic_vector(64-1 downto 0);
signal RX_MVB_VLD  : std_logic; --WR_EN

signal RD_DATA     : std_logic_vector(64-1 downto 0);
signal RD_EN       : std_logic;

signal RD_DATA_VLD : std_logic;

begin
   ram: RAMB36E1
      generic map (
         RAM_MODE       => "SDP",
         READ_WIDTH_A   => 72
      )
      port map (
         --! Clock
         CLKBWRCLK      => WR_CLK,
         CLKARDCLK      => RD_CLK,
         --! Reset
         RSTRAMARSTRAM  => WR_RESET,
         -- => RD_RESET,
         --! Address
         ADDRBWRADDR    => WR_ADDR,
         ADDRARDADDR    => RD_ADDR,
         --! Input
         DIADI          => RX_MVB_DATA(31 downto 0),
         DIBDI          => RX_MVB_DATA(63 downto 32),
         ENBWREN        => RX_MVB_VLD,
         --! Output
         DOADO          => RD_DATA(31 downto 0),
         DOBDO          => RD_DATA(63 downto 32),
         ENARDEN        => RD_EN,
         --! Other
         REGCEAREGCE    => '1',
         REGCEB         => '1',
         CASCADEINA     => '0',
         CASCADEINB     => '0',
         INJECTDBITERR  => '0',
         INJECTSBITERR  => '0',
         RSTRAMB        => '0',
         RSTREGARSTREG  => '0',
         RSTREGB        => '0',
         DIPADIP        => (others => 'X'),
         DIPBDIP        => (others => 'X'),
         WEA            => (others => '1'),
         WEBWE          => (others => '1')
      );

   led : entity work.led_ctrl_top
      generic map   (
         LED_COUNT         => 3,
         ON_VALUE          => '0',
         CLK_PERIOD        => 10,
         PTRN_STEP_PERIOD  => 5,
         PTRN_LENGTH       => 8
      )

      port map (
         CLK         => CLK,
         RESET       => RESET,

         PTRNS       => ptrn_2 & ptrn_1 & ptrn_0,

         LED_GREEN   => LED_GREEN,
         LED_RED     => LED_RED
      );

   CLK <= not CLK after 10 ns;
   RESET <= '0' after 10 ms;

end Behavioral;
