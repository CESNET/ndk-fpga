-- testbench.vhd: Simulation file 
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): David Beneš <benes.david2000@seznam.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE IEEE.std_logic_textio.ALL;
USE ieee.numeric_std.ALL;
USE std.textio.ALL;
 
ENTITY TESTBENCH IS
END TESTBENCH;
 
ARCHITECTURE FULL OF TESTBENCH IS 

   --Inputs
   signal clk200              : std_logic;
   signal clk250              : std_logic;
   signal rst                 : std_logic;

   --bmc_driver
   signal spi_miso            : std_logic;
   signal spi_int             : std_logic;
   signal bmc_mi_addr         : std_logic_vector(8 - 1 downto 0);
   signal bmc_mi_dwr          : std_logic_vector(32 - 1 downto 0);
   signal bmc_mi_wr           : std_logic;
   signal bmc_mi_rd           : std_logic;
   signal bmc_mi_be           : std_logic_vector(3 downto 0);


   --Outputs
   signal spi_clk             : std_logic;
   signal spi_nss             : std_logic;     
   signal spi_mosi            : std_logic;     
   signal bmc_mi_ardy         : std_logic;
   signal bmc_mi_drd          : std_logic_vector(32 - 1 downto 0);
   signal bmc_mi_drdy         : std_logic; 

      
   
   -- Clock period definitions
   constant clk_period250 : time := 4 ns;
   constant clk_period200 : time := 5 ns;

   signal miso_data       : std_logic_vector(15 downto 0):= x"F0F0";
                          
BEGIN
 
    -- Instantiate the Unit Under Test (UUT)
        
   uut_i: entity work.BMC_DRIVER
      PORT MAP(
            CLK                => clk250,
            RST                => rst,
            SPI_CLK            => spi_clk,
            SPI_NSS            => spi_nss,
            SPI_MOSI           => spi_mosi,
            SPI_MISO           => spi_miso,
            SPI_INT            => spi_int,
            BMC_MI_ADDR        => bmc_mi_addr,
            BMC_MI_DWR         => bmc_mi_dwr,
            BMC_MI_WR          => bmc_mi_wr,
            BMC_MI_RD          => bmc_mi_rd,
            BMC_MI_BE          => bmc_mi_be,
            BMC_MI_ARDY        => bmc_mi_ardy,
            BMC_MI_DRD         => bmc_mi_drd,
            BMC_MI_DRDY        => bmc_mi_drdy
      );
   
   -- Clock process definitions
   clk250_p :process
   begin
        clk250 <= '0';
        wait for clk_period250/2;
        clk250 <= '1';
        wait for clk_period250/2;
   end process;

   -- Clock process definitions
   clk200_p :process
   begin
         clk200 <= '0';
         wait for clk_period200/2;
         clk200 <= '1';
         wait for clk_period200/2;
   end process;
 

   rd_p: process
   begin

      wait until spi_clk = '1';
      spi_miso    <= '1';

   end process;


   int_p: process
   begin
      spi_int <= '0';
      wait for 2000 us;
         spi_int <= '1';
      wait for 200000 ns;
   end process;

   -- Stimulus process
   stim_proc: process
   begin        
      rst <= '1', '0' after clk_period250*5;
      spi_miso    <= '1';

      wait for 10 us;
      bmc_mi_addr       <= x"00";
      bmc_mi_wr         <= '1';
      bmc_mi_rd         <= '1';
      bmc_mi_dwr        <= x"A0A0A0A0";
      wait for clk_period250;
      bmc_mi_wr         <= '1';
      bmc_mi_addr       <= x"04";
      bmc_mi_dwr        <= x"CCCCA0A0";
      wait for clk_period250;
      bmc_mi_addr       <= x"00";
      bmc_mi_wr         <= '0';

      wait for clk_period250*1000000;

      spi_miso    <= '1';

      wait for 10 us;
      bmc_mi_addr       <= x"00";
      bmc_mi_wr         <= '1';
      bmc_mi_rd         <= '1';
      bmc_mi_dwr        <= x"A0A0A0A0";
      wait for clk_period250;
      bmc_mi_wr         <= '1';
      bmc_mi_addr       <= x"04";
      bmc_mi_dwr        <= x"CCCCA0A0";
      wait for clk_period250;
      bmc_mi_addr       <= x"00";

      bmc_mi_wr         <= '0';


      wait for clk_period250*100;  

      WAIT;
   end process;

END;
