-- bootfpga_mi_x16.vhd : Component for work with parallel x16 flash
--!
--! \file
--! \brief Parallel asynchronous flash interface & FPGA boot component
--! \author Martin Spinler <spinler@cesnet.cz>
--! \author Stepan Friedl <friedl@cesnet.cz>
--! \date 2015
--!
--! \section License
--!
--! Copyright (C) 2015 CESNET
--!
--! SPDX-License-Identifier: BSD-3-Clause
--!

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use ieee.numeric_std.all;

entity bootfpga_flash_mi is
generic ( CLK_PERIOD : natural := 8 );
port(
   CLK         : in  std_logic;
   RESET       : in  std_logic;

   MI_DWR      : in  std_logic_vector(31 downto 0);
   MI_ADDR     : in  std_logic_vector(31 downto 0);
   MI_RD       : in  std_logic;
   MI_WR       : in  std_logic;
   MI_BE       : in  std_logic_vector(3 downto 0);
   MI_DRD      : out std_logic_vector(31 downto 0);
   MI_ARDY     : out std_logic;
   MI_DRDY     : out std_logic;
   --
   -- Flash address
   AD        : out std_logic_vector(26 downto 0 );
   -- Data from flash
   D_I       : in  std_logic_vector(15 downto 0 );
   -- Data to flash
   D_O       : out std_logic_vector(15 downto 0 );
   -- D output enable (HI-Z on data disable). Active high
   D_OE      : out std_logic;
   -- Chip select
   CS_N      : out std_logic;
   -- Output drivers enable
   OE_N      : out std_logic;
   -- Flash reset
   RST_N     : out std_logic;
   -- Write anable
   WE_N      : out std_logic;
   -- Synchronous mode only
   FWAIT      : in  std_logic;
   -- Synchronous mode only. Tie LOW
   ADV_N     : out std_logic;
   -- Write protect - tie HIGH
   WP_N      : out std_logic;
   -- synchronous mode flash clock - tie LOW or HIGH
   FCLK      : out std_logic

);
end bootfpga_flash_mi;

architecture full of bootfpga_flash_mi is

   signal boot_wr_data  :  std_logic_vector(63 downto 0);
   signal boot_wr_str   :  std_logic;
   signal boot_rd_data  :  std_logic_vector(63 downto 0);

   signal mi_wr_str     :  std_logic := '0';
   signal timeout       :  std_logic_vector(25 downto 0) := (others => '0');
   signal timeout_en    :  std_logic := '0';

begin

   ADV_N <= '0';
   WP_N  <= '1';
   FCLK  <= '0';

   -- INFO: X"E" is a Reload FPGA Design Command, we send it delayed. (cca 135ms @ 250 MHz)
   -- INFO: Driver must detach device from the bus first. Otherwise is raised Kernel panic

   MI_ARDY     <= MI_RD or MI_WR;
   MI_DRDY     <= MI_RD;
   boot_wr_str <= mi_wr_str or timeout(25);

   timeoutp: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            timeout_en  <= '0';
         elsif MI_WR = '1' and MI_ADDR(2) = '1' and MI_DWR(31 downto 28) = X"E" then
            timeout_en  <= '1';
         end if;

         if timeout_en = '1' and timeout(25) = '0' then
            timeout     <= timeout + 1;
         else
            timeout     <= (others =>'0');
         end if;
      end if;
   end process;

   MI_REGS: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         mi_wr_str      <= '0';

         if MI_WR = '1' then
            case MI_ADDR(2) is
               when '0' => boot_wr_data(31 downto  0) <= MI_DWR;
               when '1' => boot_wr_data(63 downto 32) <= MI_DWR;
                  if(MI_DWR(31 downto 28) /= X"E") then
                     mi_wr_str   <= '1';
                  end if;
               when others => null;
            end case;
         end if;
      end if;
   end process;

   mi_datap : process(MI_ADDR,boot_rd_data)
   begin
      case MI_ADDR(2) is
         when '0' => MI_DRD <= boot_rd_data(31 downto  0);
         when '1' => MI_DRD <= boot_rd_data(63 downto 32);
         when others => null;
      end case;
   end process;

   FLASHCTRL_I: entity work.flashctrl
   generic map ( CLK_PERIOD => 4 )
   port map (
      RESET  => RESET,
      CLK    => CLK,
      -- Command interface
      DWR    => boot_wr_data,
      DWR_WR => boot_wr_str,
      DRD    => boot_rd_data,
      -- FLASH interface --
      AD     => AD,
      D_I    => D_I,
      D_O    => D_O,
      D_OE   => D_OE,
      CS_N   => CS_N,
      OE_N   => OE_N,
      RST_N  => RST_N,
      WE_N   => WE_N
   );

end full;
