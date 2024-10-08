-- boot_ctrl.vhd: Simple boot controller
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity BOOT_CTRL is
    generic(
        -- ICAP WBSTAR register value (see UG570) for boot image 0 (Xilinx Only):
        -- [31:30] = RS[1:0] pin value on next warm boot in BPI mode. The default is 00.
        --    [29] = RS[1:0] pins 3-state enable: 
        --             0 = 3-state enabled (RS[1:0] disabled) (default)
        --             1 = 3-state disabled (RS[1:0] enabled)
        --  [28:0] = START_ADDR: Next bitstream start address.
        --           The default start address is address zero.
        ICAP_WBSTAR0   : std_logic_vector(31 downto 0) := X"00000000";
        -- ICAP WBSTAR register value (see UG570) for boot image 1 (Xilinx Only):
        -- [31:30] = RS[1:0] pin value on next warm boot in BPI mode. The default is 00.
        --    [29] = RS[1:0] pins 3-state enable: 
        --             0 = 3-state enabled (RS[1:0] disabled) (default)
        --             1 = 3-state disabled (RS[1:0] enabled)
        --  [28:0] = START_ADDR: Next bitstream start address.
        --           The default start address is address zero. 
        ICAP_WBSTAR1   : std_logic_vector(31 downto 0) := X"01002000";
        -- FPGA device (ULTRASCALE, AGILEX,...)
        DEVICE         : string  := "ULTRASCALE";
        -- BOOT type (supported values: 1, 2, 3)
        BOOT_TYPE      : natural := 2;
        -- BOOT timeout width in bites
        BOOT_TIMEOUT_W : natural := 26
    ); 
    port(
        -- =====================================================================
        -- MAIN MI slave interface (MI_CLK)
        -- =====================================================================
        MI_CLK        : in  std_logic;
        MI_RESET      : in  std_logic;
        MI_DWR        : in  std_logic_vector(31 downto 0);
        MI_ADDR       : in  std_logic_vector(31 downto 0);
        MI_RD         : in  std_logic;
        MI_WR         : in  std_logic;
        MI_BE         : in  std_logic_vector(3 downto 0);
        MI_DRD        : out std_logic_vector(31 downto 0);
        MI_ARDY       : out std_logic;
        MI_DRDY       : out std_logic;

        -- =====================================================================
        -- BOOT clock, reset and control signals (BOOT_CLK)
        -- =====================================================================
        BOOT_CLK      : in  std_logic;
        BOOT_RESET    : in  std_logic;

        BOOT_REQUEST  : out std_logic;
        BOOT_IMAGE    : out std_logic;

        -- =====================================================================
        -- Interface to Generic Flash controller (BOOT_CLK)
        -- =====================================================================
        FLASH_WR_DATA : out std_logic_vector(63 downto 0);
        FLASH_WR_EN   : out std_logic;
        FLASH_RD_DATA : in  std_logic_vector(63 downto 0) := (others => '0');

        -- =====================================================================
        -- ICAP interface (BOOT_CLK)
        -- =====================================================================
        ICAP_AVAIL  : in  std_logic := '0';
        ICAP_CSIB   : out std_logic;
        ICAP_RDWRB  : out std_logic;
        ICAP_DI     : out std_logic_vector(32-1 downto 0);
        ICAP_DO     : in  std_logic_vector(32-1 downto 0) := (others => '0');

        -- =====================================================================
        -- MI master interface for AXI QSPI controller (BOOT_CLK)
        -- =====================================================================
        AXI_MI_ADDR : out std_logic_vector(8 - 1 downto 0);
        AXI_MI_DWR  : out std_logic_vector(32 - 1 downto 0);
        AXI_MI_WR   : out std_logic;
        AXI_MI_RD   : out std_logic;
        AXI_MI_BE   : out std_logic_vector((32/8)-1 downto 0);
        AXI_MI_ARDY : in  std_logic :='0';
        AXI_MI_DRD  : in  std_logic_vector(32 - 1 downto 0) := (others => '0');
        AXI_MI_DRDY : in  std_logic :='0';

        -- =====================================================================
        -- MI master interface for custom BMC controller (BOOT_CLK)
        -- =====================================================================
        BMC_MI_ADDR : out std_logic_vector(8 - 1 downto 0);
        BMC_MI_DWR  : out std_logic_vector(32 - 1 downto 0);
        BMC_MI_WR   : out std_logic;
        BMC_MI_RD   : out std_logic;
        BMC_MI_BE   : out std_logic_vector((32/8)-1 downto 0);
        BMC_MI_ARDY : in  std_logic :='0';
        BMC_MI_DRD  : in  std_logic_vector(32 - 1 downto 0) := (others => '0');
        BMC_MI_DRDY : in  std_logic :='0'
    );
end entity;

architecture FULL of BOOT_CTRL is
    -- MI SPLITTER
    constant MI_BOOT_PORTS : natural := 2;
    constant MI_BOOT_ADDR_BASE : slv_array_t(MI_BOOT_PORTS-1 downto 0)(32-1 downto 0)
    := ( 0 => X"0000_0000",     -- BMC
         1 => X"0000_2100");    -- AXI Quad SPI 
    constant MASK :std_logic_vector(32 -1 downto 0):=(8 => '1', others => '0');

    -- MI ASYNC
    signal mi_sync_dwr       : std_logic_vector(31 downto 0);
    signal mi_sync_addr      : std_logic_vector(31 downto 0);
    signal mi_sync_rd        : std_logic;
    signal mi_sync_wr        : std_logic;
    signal mi_sync_be        : std_logic_vector(3 downto 0);
    signal mi_sync_drd       : std_logic_vector(31 downto 0);
    signal mi_sync_ardy      : std_logic;
    signal mi_sync_drdy      : std_logic;
    -- MI SPLITTER
    signal mi_split_dwr      : slv_array_t(MI_BOOT_PORTS-1 downto 0)(31 downto 0);
    signal mi_split_addr     : slv_array_t(MI_BOOT_PORTS-1 downto 0)(31 downto 0);
    signal mi_split_rd       : std_logic_vector(MI_BOOT_PORTS-1 downto 0);
    signal mi_split_wr       : std_logic_vector(MI_BOOT_PORTS-1 downto 0);
    signal mi_split_be       : slv_array_t(MI_BOOT_PORTS-1 downto 0)( 3 downto 0);
    signal mi_split_drd      : slv_array_t(MI_BOOT_PORTS-1 downto 0)(31 downto 0):=(others => (others => '0'));
    signal mi_split_ardy     : std_logic_vector(MI_BOOT_PORTS-1 downto 0);
    signal mi_split_drdy     : std_logic_vector(MI_BOOT_PORTS-1 downto 0):=(others => '0');
    -- MI BOOT
    signal mi_boot_dwr       : std_logic_vector(31 downto 0);
    signal mi_boot_addr      : std_logic_vector(31 downto 0);
    signal mi_boot_rd        : std_logic;
    signal mi_boot_wr        : std_logic;
    signal mi_boot_be        : std_logic_vector(3 downto 0);
    signal mi_boot_drd       : std_logic_vector(31 downto 0);
    signal mi_boot_ardy      : std_logic;
    signal mi_boot_drdy      : std_logic;

    signal boot_cmd          : std_logic := '0';
    signal boot_img          : std_logic := '0';
    signal boot_timeout      : unsigned(BOOT_TIMEOUT_W-1 downto 0) := (others => '0');
    signal flash_wr_data_reg : std_logic_vector(64-1 downto 0);
    signal flash_wr_cmd      : std_logic := '0';

    signal icap_di_orig      : std_logic_vector(32-1 downto 0);
    signal icap_di_swap      : std_logic_vector(32-1 downto 0);
    signal icap_boot_addr    : std_logic_vector(32-1 downto 0);
    signal icap_state_cnt    : unsigned(4-1 downto 0) := (others => '0');

    type t_rom_8x32 is array (0 to 15) of std_logic_vector (31 downto 0);
    constant icap_rom : t_rom_8x32 := (X"FFFFFFFF",  -- 0 = Dummy
                                       X"FFFFFFFF",  -- 1 = Dummy
                                       X"AA995566",  -- 2 = Sync
                                       X"20000000",  -- 3 = NoOP
                                       X"30020001",  -- 4 = Write 1 Word to WBSTAR
                                       X"00000000",  -- 5 = Boot address
                                       X"30008001",  -- 6 = Write 1 Word to CMD
                                       X"0000000F",  -- 7 = IPROG
                                       X"20000000",  -- 8 = NoOP
                                       X"FFFFFFFF",  -- 9 = Dummy
                                       X"FFFFFFFF",  -- A = Dummy
                                       X"FFFFFFFF",  -- B = Dummy
                                       X"FFFFFFFF",  -- C = Dummy
                                       X"FFFFFFFF",  -- D = Dummy
                                       X"FFFFFFFF",  -- E = Dummy
                                       X"FFFFFFFF"); -- F = Dummy
begin

    mi_async_i : entity work.MI_ASYNC
    generic map(
        DEVICE => DEVICE
    )
    port map(
        -- Master interface
        CLK_M     => MI_CLK,
        RESET_M   => MI_RESET,
        MI_M_DWR  => MI_DWR,
        MI_M_ADDR => MI_ADDR,
        MI_M_RD   => MI_RD,
        MI_M_WR   => MI_WR,
        MI_M_BE   => MI_BE,
        MI_M_DRD  => MI_DRD,
        MI_M_ARDY => MI_ARDY,
        MI_M_DRDY => MI_DRDY,

        -- Slave interface
        CLK_S     => BOOT_CLK,
        RESET_S   => BOOT_RESET,
        MI_S_DWR  => mi_sync_dwr,
        MI_S_ADDR => mi_sync_addr,
        MI_S_RD   => mi_sync_rd,
        MI_S_WR   => mi_sync_wr,
        MI_S_BE   => mi_sync_be,
        MI_S_DRD  => mi_sync_drd,
        MI_S_ARDY => mi_sync_ardy,
        MI_S_DRDY => mi_sync_drdy
    );

    boot_type_1_or_3_g: if ((BOOT_TYPE = 1) or (BOOT_TYPE = 3)) generate
        mi_splitter_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH    => 32,
            DATA_WIDTH    => 32,
            PORTS         => MI_BOOT_PORTS,
            PIPE_OUTREG   => true,
            ADDR_BASE     => MI_BOOT_ADDR_BASE,
            ADDR_MASK     => MASK,
            DEVICE        => DEVICE
        )
        port map(
            CLK        => BOOT_CLK,
            RESET      => BOOT_RESET,
    
            RX_DWR     => mi_sync_dwr,
            RX_ADDR    => mi_sync_addr,
            RX_BE      => mi_sync_be,
            RX_RD      => mi_sync_rd,
            RX_WR      => mi_sync_wr,
            RX_ARDY    => mi_sync_ardy,
            RX_DRD     => mi_sync_drd,
            RX_DRDY    => mi_sync_drdy,
    
            TX_DWR     => mi_split_dwr,
            TX_ADDR    => mi_split_addr,
            TX_BE      => mi_split_be,
            TX_RD      => mi_split_rd,
            TX_WR      => mi_split_wr,
            TX_ARDY    => mi_split_ardy,
            TX_DRD     => mi_split_drd,
            TX_DRDY    => mi_split_drdy
        );

        -- MI interface for Axi Quad SPI IP
        AXI_MI_ADDR         <= mi_split_addr(1)(8-1  downto 0);
        AXI_MI_DWR          <= mi_split_dwr(1);
        AXI_MI_WR           <= mi_split_wr(1);
        AXI_MI_RD           <= mi_split_rd(1);
        AXI_MI_BE           <= mi_split_be(1);
        mi_split_ardy(1)    <= AXI_MI_ARDY;
        mi_split_drd(1)     <= AXI_MI_DRD;
        mi_split_drdy(1)    <= AXI_MI_DRDY;

        -- MI interface for boot logic
        mi_boot_addr     <= mi_split_addr(0);
        mi_boot_dwr      <= mi_split_dwr(0);
        mi_boot_wr       <= mi_split_wr(0);
        mi_boot_rd       <= mi_split_rd(0);
        mi_boot_be       <= mi_split_be(0);
        mi_split_ardy(0) <= mi_boot_ardy;
        mi_split_drd(0)  <= mi_boot_drd;
        mi_split_drdy(0) <= mi_boot_drdy;
    else generate
        -- NO MI Splitter
        mi_boot_addr <= mi_sync_addr;
        mi_boot_dwr  <= mi_sync_dwr;
        mi_boot_wr   <= mi_sync_wr;
        mi_boot_rd   <= mi_sync_rd;
        mi_boot_be   <= mi_sync_be;
        mi_sync_ardy <= mi_boot_ardy;
        mi_sync_drd  <= mi_boot_drd;
        mi_sync_drdy <= mi_boot_drdy;
    end generate;

    -- MI interface for BMC device controller (only TYPE=3)
    bmc_g: if (BOOT_TYPE = 3) generate
        BMC_MI_ADDR  <= mi_boot_addr(8-1 downto 0);
        BMC_MI_DWR   <= mi_boot_dwr;
        BMC_MI_WR    <= mi_boot_wr;
        BMC_MI_RD    <= mi_boot_rd;
        BMC_MI_BE    <= mi_boot_be;
        mi_boot_ardy <= BMC_MI_ARDY;
        mi_boot_drd  <= BMC_MI_DRD;
        mi_boot_drdy <= BMC_MI_DRDY;
    end generate;

    boot_type_1_or_2_g: if ((BOOT_TYPE = 1) or (BOOT_TYPE = 2)) generate
        mi_boot_ardy <= (mi_boot_rd or mi_boot_wr);

        mi_rd_p : process(BOOT_CLK)
        begin
            if rising_edge(BOOT_CLK) then
                case mi_boot_addr(3 downto 2) is
                    when "00"   => mi_boot_drd <= FLASH_RD_DATA(31 downto  0);
                    when "01"   => mi_boot_drd <= FLASH_RD_DATA(63 downto 32);
                    when "10"   => mi_boot_drd <= X"0000000" & '0' & ICAP_RDWRB & ICAP_CSIB & ICAP_AVAIL;
                    when "11"   => mi_boot_drd <= ICAP_DI;
                    when others => mi_boot_drd <= (others => '0');
                end case;
                mi_boot_drdy <= mi_boot_rd;
                    
                if (BOOT_RESET = '1') then
                    mi_boot_drdy <= '0';
                end if;
            end if;
        end process;
    
        mi_wr_p : process(BOOT_CLK)
        begin
            if rising_edge(BOOT_CLK) then
                flash_wr_cmd <= '0';
                if (mi_boot_wr = '1' and boot_cmd = '0') then
                    case mi_boot_addr(3 downto 2) is
                        when "00" =>
                            flash_wr_data_reg(31 downto  0) <= mi_boot_dwr;
                        when "01" =>
                            flash_wr_data_reg(63 downto 32) <= mi_boot_dwr;
                            flash_wr_cmd <= '1';
                            -- Reboot FPGA command
                            if (mi_boot_dwr(31 downto 28) = X"E") then
                                flash_wr_cmd <= '0';
                                boot_cmd <= '1';
                                boot_img <= not flash_wr_data_reg(0);
                            end if;
            
                        when others => null;
                    end case;            
                end if;
    
                if (BOOT_RESET = '1') then
                    boot_cmd <= '0';
                end if;
            end if;
        end process;
        
        boot_timeout_p : process(BOOT_CLK)
        begin
            if rising_edge(BOOT_CLK) then
                if (boot_cmd = '1') then
                    boot_timeout <= boot_timeout + 1;
                else
                    boot_timeout <= (others =>'0');
                end if;
            end if;
        end process;
    
        BOOT_REQUEST <= boot_cmd and (boot_timeout(BOOT_TIMEOUT_W-1));
        BOOT_IMAGE   <= boot_img;
    end generate;

    flash_g: if (BOOT_TYPE = 2) generate
        FLASH_WR_DATA <= flash_wr_data_reg;
        FLASH_WR_EN   <= flash_wr_cmd or BOOT_REQUEST;
    else generate
        FLASH_WR_DATA <= (others => '0');
        FLASH_WR_EN   <= '0';
    end generate;

    icap_g: if (BOOT_TYPE = 1) generate
        process(BOOT_CLK)
        begin
            if rising_edge(BOOT_CLK) then
                if (BOOT_RESET = '1') then
                    icap_state_cnt <= X"0";
                    ICAP_CSIB      <= '1'; -- ICAP enable active in low
                elsif (icap_state_cnt = X"0") and (BOOT_REQUEST = '1') and (ICAP_AVAIL = '1') then
                    icap_state_cnt <= X"1"; -- run boot sequence when is set boot request
                    ICAP_CSIB      <= '0';
                elsif (icap_state_cnt = X"0") then
                    icap_state_cnt <= X"0"; -- stay in idle state
                    ICAP_CSIB      <= '1';
                elsif (icap_state_cnt = X"9") then
                    icap_state_cnt <= X"9"; -- stay in dummy state, boot request done
                    ICAP_CSIB      <= '1';
                else
                    icap_state_cnt <= icap_state_cnt + 1;
                    ICAP_CSIB      <= '0';
                end if;
            end if;
        end process;

        icap_boot_addr <= ICAP_WBSTAR1 when (boot_img = '1') else ICAP_WBSTAR0;
        icap_di_orig   <= icap_boot_addr when (icap_state_cnt = 5) else icap_rom(to_integer(icap_state_cnt));

        icap_di_swap_g: for i in 0 to 3 generate
            icap_di_swap_g2: for j in 0 to 7 generate
                icap_di_swap((i*8)+j) <= icap_di_orig((i*8)+(7-j));
            end generate; 
        end generate; 

        ICAP_RDWRB <= '0';
        ICAP_DI    <= icap_di_swap;
    else generate
        ICAP_CSIB  <= '1';
        ICAP_RDWRB <= '0';
        ICAP_DI    <= (others => '0');
    end generate;
    
end architecture;
