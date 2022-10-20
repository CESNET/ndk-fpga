-- This file was generated automatically. For changing its content,
-- edit corresponding variables in ndk_const.tcl

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;

package combo_user_const is
--   constant ID_PROJECT_TEXT : std_logic_vector( 255 downto 0) := X"0000000000000000000000000000000000000000000000000000000000000000";
    constant ETH_PORTS : integer := 1;
--   constant ETH_PORT_SPEED : integer_vector( 0 downto 0) := (others => 400);
--   constant ETH_PORT_CHAN : integer_vector( 0 downto 0) := (others => 1);
    constant ETH_PORT_RX_MTU : integer_vector( 0 downto 0) := (others => 2**12);
    constant ETH_PORT_TX_MTU : integer_vector( 0 downto 0) := (others => 2**12);
--   constant PCIE_ENDPOINTS : integer := 1;
--   constant PCIE_ENDPOINT_MODE : integer := 1;
--   constant DMA_RX_CHANNELS : integer := 4;
--   constant DMA_TX_CHANNELS : integer := 4;
--   constant DMA_RX_BLOCKING_MODE : boolean := false;
--   constant DMA_RX_FRAME_SIZE_MAX : integer := 2**12;
--   constant DMA_TX_FRAME_SIZE_MAX : integer := 2**12;
--   constant DMA_CROX_CLK_SEL : integer := 0;
--   constant TSU_ENABLE : boolean := false;
--   constant TSU_FREQUENCY : integer := 161132812;
--   constant RESET_WIDTH : integer := 10;
--   constant DMA_400G_DEMO : boolean := false;

end combo_user_const;

package body combo_user_const is
end combo_user_const;
