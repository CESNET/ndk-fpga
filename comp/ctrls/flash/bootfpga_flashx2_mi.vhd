-- bootfpga_mi.vhd : Component for work with parallel x32 flash (two x16 FLASH
--                   chips with separate control+data and common address)
--!
--! \file
--! \brief PLDA40G1 flash interface & FPGA boot component
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

entity bootfpga_flashx2_mi is
generic (
   CLK_PERIOD : natural := 8
);
port(
   CLK         : in  std_logic;
   RESET       : in  std_logic;

   -- ============
   -- MI interface
   -- ============

   MI_DWR      : in  std_logic_vector(31 downto 0);
   MI_ADDR     : in  std_logic_vector(31 downto 0);
   MI_RD       : in  std_logic;
   MI_WR       : in  std_logic;
   MI_BE       : in  std_logic_vector(3 downto 0);
   MI_DRD      : out std_logic_vector(31 downto 0);
   MI_ARDY     : out std_logic;
   MI_DRDY     : out std_logic;
   -- ==============
   -- FLASH common
   --
   -- address + data
   -- ==============

   -- Flash address
   AD        : out std_logic_vector(26 downto 0 );
   -- Data from flash
   D_I       : in  std_logic_vector(31 downto 0 );
   -- Data to flash
   D_O       : out std_logic_vector(31 downto 0 );
   -- synchronous mode flash clock
   FCLK      : out std_logic;

   -- ==============
   -- FLASH1 control
   -- ==============

   -- D output enable (HI-Z on data disable). Active high
   D_OE_1    : out std_logic;
   -- Chip select
   CS_N_1    : out std_logic;
   -- Output drivers enable
   OE_N_1    : out std_logic;
   -- Flash reset
   RST_N_1   : out std_logic;
   -- Write anable
   WE_N_1    : out std_logic;
   -- Synchronous mode only
   FWAIT_1   : in  std_logic;
   -- Synchronous mode only
   ADV_N_1   : out std_logic;
   -- Write protect
   WP_N_1    : out std_logic;

   -- ==============
   -- FLASH2 control
   -- ==============

   -- D output enable (HI-Z on data disable). Active high
   D_OE_2    : out std_logic;
   -- Chip select
   CS_N_2    : out std_logic;
   -- Output drivers enable
   OE_N_2    : out std_logic;
   -- Flash reset
   RST_N_2   : out std_logic;
    -- Write anable
   WE_N_2    : out std_logic;
   -- Synchronous mode only
   FWAIT_2   : in  std_logic;
   -- Synchronous mode only
   ADV_N_2   : out std_logic;
   -- Write protect
   WP_N_2    : out std_logic
);
end bootfpga_flashx2_mi;

architecture full of bootfpga_flashx2_mi is

   signal boot1_wr_data :  std_logic_vector(63 downto 0);
   signal boot1_rd_data :  std_logic_vector(63 downto 0);
   signal boot2_wr_data :  std_logic_vector(63 downto 0);
   signal boot2_rd_data :  std_logic_vector(63 downto 0);
   signal boot1_wr_str  :  std_logic;
   signal boot2_wr_str  :  std_logic;

   signal ad1           :  std_logic_vector(AD'range);
   signal ad2           :  std_logic_vector(AD'range);

   signal timeout       :  std_logic_vector(25 downto 0) := (others => '0');
   signal timeout_en    :  std_logic := '0';

begin

   ADV_N_1 <= '0';
   WP_N_1  <= '1';
   ADV_N_2 <= '0';
   WP_N_2  <= '1';
   FCLK    <= '0';

   MI_ARDY     <= MI_RD or MI_WR;
   MI_DRDY     <= MI_RD;

   -- INFO: X"E" is a Reload FPGA Design Command, we send it delayed. (cca 135ms @ 250 MHz)
   -- INFO: Driver must detach device from the bus first. Otherwise is raised Kernel panic

--    timeoutp: process(CLK)
--    begin
--       if CLK'event and CLK = '1' then
--          if RESET = '1' then
--             timeout_en  <= '0';
--          elsif MI_WR = '1' and MI_ADDR(2) = '1' and MI_DWR(31 downto 28) = X"E" then
--             timeout_en  <= '1';
--          end if;
--
--          if timeout_en = '1' and timeout(25) = '0' then
--             timeout     <= timeout + 1;
--          else
--             timeout     <= (others =>'0');
--          end if;
--       end if;
--    end process;

   MI_REGS: process(CLK)
   begin
      if CLK'event and CLK = '1' then
         boot1_wr_str  <= '0';
         boot2_wr_str  <= '0';

         if MI_WR = '1' then
            case MI_ADDR(3 downto 2) is
               when "00" => boot1_wr_data(31 downto  0) <= MI_DWR;
               when "01" => boot1_wr_data(63 downto 32) <= MI_DWR;
                  if(MI_DWR(31 downto 28) /= X"E") then
                     boot1_wr_str   <= '1';
                  end if;
               when "10" => boot2_wr_data(31 downto  0) <= MI_DWR;
               when "11" => boot2_wr_data(63 downto 32) <= MI_DWR;
                  if(MI_DWR(31 downto 28) /= X"E") then
                     boot2_wr_str   <= '1';
                  end if;
               when others => null;
            end case;
         end if;
      end if;
   end process;

   mi_datap : process(MI_ADDR,boot1_rd_data,boot2_rd_data)
   begin
      case MI_ADDR(3 downto 2) is
         when "00" =>
            MI_DRD(15 downto 0) <= boot1_rd_data(15 downto  0);
            MI_DRD(16)          <= boot1_rd_data(16) and boot2_rd_data(16); -- Ready flag
            MI_DRD(31 downto 17)<= boot1_rd_data(31 downto 17);
         when "01" =>
            MI_DRD              <= boot1_rd_data(63 downto 32);
         when "10" =>
            MI_DRD(15 downto 0) <= boot2_rd_data(15 downto  0);
            MI_DRD(16)          <= boot2_rd_data(16) and boot1_rd_data(16); -- Ready flag
            MI_DRD(31 downto 17)<= boot2_rd_data(31 downto 17);
         when "11" =>
            MI_DRD              <= boot2_rd_data(63 downto 32);
         when others => null;
      end case;
   end process;

   ----------------------------------------------------------------------------
   -- First flash controller - LOW data words -------------------------------
   ----------------------------------------------------------------------------

   FLASHCTRL1_I: entity work.flashctrl
   generic map ( CLK_PERIOD => CLK_PERIOD )
   port map (
      RESET  => RESET,
      CLK    => CLK,
      -- Command interface
      DWR    => boot1_wr_data,
      DWR_WR => boot1_wr_str,
      DRD    => boot1_rd_data,
      -- FLASH interface --
      AD     => ad1,
      D_I    => D_I(15 downto 0),
      D_O    => D_O(15 downto 0),
      D_OE   => D_OE_1,
      CS_N   => CS_N_1,
      OE_N   => OE_N_1,
      RST_N  => RST_N_1,
      WE_N   => WE_N_1
   );

   ----------------------------------------------------------------------------
   -- Second flash controller - HIGH data words -------------------------------
   ----------------------------------------------------------------------------

   FLASHCTRL2_I: entity work.flashctrl
   generic map ( CLK_PERIOD => CLK_PERIOD )
   port map (
      RESET  => RESET,
      CLK    => CLK,
      -- Command interface
      DWR    => boot2_wr_data,
      DWR_WR => boot2_wr_str,
      DRD    => boot2_rd_data,
      -- FLASH interface --
      AD     => ad2,
      D_I    => D_I(31 downto 16),
      D_O    => D_O(31 downto 16),
      D_OE   => D_OE_2,
      CS_N   => CS_N_2,
      OE_N   => OE_N_2,
      RST_N  => RST_N_2,
      WE_N   => WE_N_2
   );

   -- Address multiplexer
   AD <= ad2 when boot2_rd_data(16) = '0' else ad1;

end full;
