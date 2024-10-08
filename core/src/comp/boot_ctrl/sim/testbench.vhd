-- testbench.vhd: Simulation file 
-- Copyright (C) 2024 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
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

    signal mi_clk        : std_logic;
    signal mi_reset      : std_logic;
    signal mi_dwr        : std_logic_vector(31 downto 0);
    signal mi_addr       : std_logic_vector(31 downto 0);
    signal mi_rd         : std_logic;
    signal mi_wr         : std_logic;
    signal mi_be         : std_logic_vector(3 downto 0);
    signal mi_drd        : std_logic_vector(31 downto 0);
    signal mi_ardy       : std_logic;
    signal mi_drdy       : std_logic;
    signal boot_clk      : std_logic;
    signal boot_reset    : std_logic;
    signal boot_request  : std_logic;
    signal boot_image    : std_logic;
    signal flash_wr_data : std_logic_vector(63 downto 0);
    signal flash_wr_en   : std_logic;
    signal flash_rd_data : std_logic_vector(63 downto 0) := (others => '0');
    signal icap_avail    : std_logic := '0';
    signal icap_csib     : std_logic;
    signal icap_rdwrb    : std_logic := '0';
    signal icap_di       : std_logic_vector(32-1 downto 0);
    signal icap_do       : std_logic_vector(32-1 downto 0) := (others => '0');
    signal axi_mi_addr   : std_logic_vector(8 - 1 downto 0);
    signal axi_mi_dwr    : std_logic_vector(32 - 1 downto 0);
    signal axi_mi_wr     : std_logic;
    signal axi_mi_rd     : std_logic;
    signal axi_mi_be     : std_logic_vector((32/8)-1 downto 0);
    signal axi_mi_ardy   : std_logic :='0';
    signal axi_mi_drd    : std_logic_vector(32 - 1 downto 0) := (others => '0');
    signal axi_mi_drdy   : std_logic :='0';
    signal bmc_mi_addr   : std_logic_vector(8 - 1 downto 0);
    signal bmc_mi_dwr    : std_logic_vector(32 - 1 downto 0);
    signal bmc_mi_wr     : std_logic;
    signal bmc_mi_rd     : std_logic;
    signal bmc_mi_be     : std_logic_vector((32/8)-1 downto 0);
    signal bmc_mi_ardy   : std_logic :='0';
    signal bmc_mi_drd    : std_logic_vector(32 - 1 downto 0) := (others => '0');
    signal bmc_mi_drdy   : std_logic :='0';

    constant PERIOD_MI_CLK   : time := 5 ns;
    constant PERIOD_BOOT_CLK : time := 10 ns;
                          
BEGIN
 
    -- Instantiate the Unit Under Test (UUT)
    uut_i: entity work.BOOT_CTRL
    generic map(
        BOOT_TYPE      => 1,
        BOOT_TIMEOUT_W => 18
    )
    PORT MAP(
        MI_CLK        => mi_clk,
        MI_RESET      => mi_reset,
        MI_DWR        => mi_dwr,
        MI_ADDR       => mi_addr,
        MI_RD         => mi_rd,
        MI_WR         => mi_wr,
        MI_BE         => mi_be,
        MI_DRD        => mi_drd,
        MI_ARDY       => mi_ardy,
        MI_DRDY       => mi_drdy,

        BOOT_CLK      => boot_clk,
        BOOT_RESET    => boot_reset,
        BOOT_REQUEST  => boot_request,
        BOOT_IMAGE    => boot_image,

        FLASH_WR_DATA => flash_wr_data,
        FLASH_WR_EN   => flash_wr_en,
        FLASH_RD_DATA => flash_rd_data,

        ICAP_AVAIL    => icap_avail,
        ICAP_CSIB     => icap_csib,
        ICAP_RDWRB    => icap_rdwrb,
        ICAP_DI       => icap_di,
        ICAP_DO       => icap_do,

        AXI_MI_ADDR   => axi_mi_addr,
        AXI_MI_DWR    => axi_mi_dwr,
        AXI_MI_WR     => axi_mi_wr,
        AXI_MI_RD     => axi_mi_rd,
        AXI_MI_BE     => axi_mi_be,
        AXI_MI_ARDY   => axi_mi_ardy,
        AXI_MI_DRD    => axi_mi_drd,
        AXI_MI_DRDY   => axi_mi_drdy,

        BMC_MI_ADDR   => bmc_mi_addr,
        BMC_MI_DWR    => bmc_mi_dwr,
        BMC_MI_WR     => bmc_mi_wr,
        BMC_MI_RD     => bmc_mi_rd,
        BMC_MI_BE     => bmc_mi_be,
        BMC_MI_ARDY   => bmc_mi_ardy,
        BMC_MI_DRD    => bmc_mi_drd,
        BMC_MI_DRDY   => bmc_mi_drdy
    );
   
    process
    begin
        mi_clk <= '0';
        wait for PERIOD_MI_CLK/2;
        mi_clk <= '1';
        wait for PERIOD_MI_CLK/2;
    end process;

    process
    begin
        boot_clk <= '0';
        wait for PERIOD_BOOT_CLK/2;
        boot_clk <= '1';
        wait for PERIOD_BOOT_CLK/2;
    end process;
    
    process
    begin   
        icap_avail <= '0';     
        boot_reset <= '1', '0' after PERIOD_BOOT_CLK*3;
        wait for 3*PERIOD_BOOT_CLK;
        icap_avail <= '1';
        wait;
    end process;

    process
    begin
        mi_addr       <= (others => '0');
        mi_wr         <= '0';
        mi_rd         <= '0';
        mi_dwr        <= (others => '0');
        mi_be         <= (others => '0');

        mi_reset <= '1', '0' after PERIOD_MI_CLK*5;

        wait for 11*PERIOD_MI_CLK;

        mi_addr       <= X"00000000";
        mi_wr         <= '1';
        mi_rd         <= '0';
        mi_dwr        <= X"00000000";
        wait for PERIOD_MI_CLK;

        mi_addr       <= X"00000004";
        mi_wr         <= '1';
        mi_rd         <= '0';
        mi_dwr        <= X"E0000000";
        wait for PERIOD_MI_CLK;

        mi_addr       <= (others => '0');
        mi_wr         <= '0';
        mi_rd         <= '0';
        mi_dwr        <= (others => '0');

        wait;
    end process;

end;
