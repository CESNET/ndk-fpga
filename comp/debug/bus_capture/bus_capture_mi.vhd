-- bus_capture_mi.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity BUS_CAPTURE_MI is
    generic(
        -- Data word width in bits.
        DATA_WIDTH : natural := 64;
        -- The number of words you can capture.
        ITEMS      : natural := 512;
        -- Select memory implementation. Options:
        -- "LUT"   - effective when ITEMS <= 64 (on Intel FPGA <= 32),
        -- "BRAM"  - effective when ITEMS  > 64 (on Intel FPGA  > 32),
        -- "URAM"  - effective when ITEMS*DATA_WIDTH >= 288000
        --           and DATA_WIDTH >= 72 (URAM is only for Xilinx Ultrascale(+)),
        -- "AUTO"  - effective implementation dependent on ITEMS and DEVICE.
        RAM_TYPE   : string  := "AUTO";
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used. Supported values are:
        -- "7SERIES", "ULTRASCALE", "STRATIX10", "ARRIA10"
        DEVICE     : string  := "ULTRASCALE"
    );
    port(
        CLK          : in  std_logic;
        RESET        : in  std_logic;

        BUS_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        BUS_VALID    : in  std_logic;
        STOP_TRIGGER : in  std_logic;

        MI_CLK       : in  std_logic;
        MI_RESET     : in  std_logic;
        MI_DWR       : in  std_logic_vector(32-1 downto 0);
        MI_ADDR      : in  std_logic_vector(32-1 downto 0);
        MI_RD        : in  std_logic;
        MI_WR        : in  std_logic;
        MI_BE        : in  std_logic_vector(4-1 downto 0);
        MI_DRD       : out std_logic_vector(32-1 downto 0);
        MI_ARDY      : out std_logic;
        MI_DRDY      : out std_logic
    );
end entity;

architecture FULL of BUS_CAPTURE_MI is

    constant DWORDS           : natural := div_roundup(DATA_WIDTH,32);
    constant DATA_WIDTH_FIXED : natural := DWORDS*32;

    signal ctl_reset    : std_logic;
    signal ctl_stop_dly : std_logic_vector(log2(ITEMS)-1 downto 0);
    signal ctl_stop_reg : std_logic;
    signal ctl_rd_setup : std_logic;
    signal ctl_rd_en    : std_logic;
    signal ctl_rd_en2   : std_logic;
    signal ctl_rd_data  : std_logic_vector(DATA_WIDTH-1 downto 0);

    signal mi_sync_dwr  : std_logic_vector(32-1 downto 0);
    signal mi_sync_addr : std_logic_vector(32-1 downto 0);
    signal mi_sync_be   : std_logic_vector(4-1 downto 0);
    signal mi_sync_rd   : std_logic;
    signal mi_sync_wr   : std_logic;
    signal mi_sync_ardy : std_logic;
    signal mi_sync_drd  : std_logic_vector(32-1 downto 0);
    signal mi_sync_drdy : std_logic;

    signal mi_pipe_dwr  : std_logic_vector(32-1 downto 0);
    signal mi_pipe_addr : std_logic_vector(32-1 downto 0);
    signal mi_pipe_be   : std_logic_vector(4-1 downto 0);
    signal mi_pipe_rd   : std_logic;
    signal mi_pipe_wr   : std_logic;
    signal mi_pipe_ardy : std_logic;
    signal mi_pipe_drd  : std_logic_vector(32-1 downto 0);
    signal mi_pipe_drdy : std_logic;

    signal cmd_reg_cs   : std_logic;
    signal dly_reg_cs   : std_logic;
    signal sel_reg_cs   : std_logic;

    signal cmd_rd_setup : std_logic;
    signal cmd_rd_en    : std_logic;
    signal cmd_reset    : std_logic;

    signal dly_reg      : std_logic_vector(32-1 downto 0);
    signal sel_reg      : std_logic_vector(32-1 downto 0);
    signal cap_reg_sel  : std_logic_vector(log2(DWORDS)-1 downto 0);
    signal cap_reg      : std_logic_vector(DATA_WIDTH_FIXED-1 downto 0);
    signal cap_reg_mux  : std_logic_vector(32-1 downto 0);
    signal status_reg   : std_logic_vector(32-1 downto 0);

begin

    -- =========================================================================
    --  CAPTURE MODULE
    -- =========================================================================

    bus_capture_i : entity work.BUS_CAPTURE
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ITEMS      => ITEMS,
        RAM_TYPE   => RAM_TYPE,
        DEVICE     => DEVICE,
        OUTPUT_REG => False
    )
    port map(
        CLK          => CLK,
        RESET        => RESET,

        BUS_DATA     => BUS_DATA,
        BUS_VALID    => BUS_VALID,
        STOP_TRIGGER => STOP_TRIGGER,

        CTL_RESET    => ctl_reset,
        CTL_STOP_DLY => ctl_stop_dly,
        CTL_STOP_REG => ctl_stop_reg,
        CTL_RD_SETUP => ctl_rd_setup,
        CTL_RD_EN    => ctl_rd_en,
        CTL_RD_DATA  => ctl_rd_data
    );

    -- =========================================================================
    --  MI32 CDC AND PIPE
    -- =========================================================================

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
        CLK_S     => CLK,
        RESET_S   => RESET,
        MI_S_DWR  => mi_sync_dwr,
        MI_S_ADDR => mi_sync_addr,
        MI_S_RD   => mi_sync_rd,
        MI_S_WR   => mi_sync_wr,
        MI_S_BE   => mi_sync_be,
        MI_S_DRD  => mi_sync_drd,
        MI_S_ARDY => mi_sync_ardy,
        MI_S_DRDY => mi_sync_drdy
    );

    mi_pipe_i : entity work.MI_PIPE
    generic map(
        DEVICE      => DEVICE,
        DATA_WIDTH  => 32,
        ADDR_WIDTH  => 32,
        PIPE_TYPE   => "REG",
        USE_OUTREG  => True,
        FAKE_PIPE   => False
    )
    port map(
        -- Common interface
        CLK      => CLK,
        RESET    => RESET,

        -- Input MI interface
        IN_DWR   => mi_sync_dwr,
        IN_ADDR  => mi_sync_addr,
        IN_RD    => mi_sync_rd,
        IN_WR    => mi_sync_wr,
        IN_BE    => mi_sync_be,
        IN_DRD   => mi_sync_drd,
        IN_ARDY  => mi_sync_ardy,
        IN_DRDY  => mi_sync_drdy,

        -- Output MI interface
        OUT_DWR  => mi_pipe_dwr,
        OUT_ADDR => mi_pipe_addr,
        OUT_RD   => mi_pipe_rd,
        OUT_WR   => mi_pipe_wr,
        OUT_BE   => mi_pipe_be,
        OUT_DRD  => mi_pipe_drd,
        OUT_ARDY => mi_pipe_ardy,
        OUT_DRDY => mi_pipe_drdy
    );

    -- =========================================================================
    --  MI32 CONTROL LOGIC
    -- =========================================================================

    mi_pipe_ardy <= mi_pipe_rd or mi_pipe_wr;

    cmd_reg_cs <= '1' when (mi_pipe_addr(7 downto 2) = "000000") else '0';
    dly_reg_cs <= '1' when (mi_pipe_addr(7 downto 2) = "000001") else '0';
    sel_reg_cs <= '1' when (mi_pipe_addr(7 downto 2) = "000010") else '0';

    cmd_rd_setup <= '1' when (mi_pipe_dwr(3 downto 0) = "0001") else '0';
    cmd_rd_en    <= '1' when (mi_pipe_dwr(3 downto 0) = "0010") else '0';
    cmd_reset    <= '1' when (mi_pipe_dwr(3 downto 0) = "0011") else '0';

    cmd_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            ctl_rd_setup <= cmd_reg_cs and mi_pipe_wr and cmd_rd_setup;
            ctl_rd_en    <= cmd_reg_cs and mi_pipe_wr and cmd_rd_en;
            ctl_reset    <= cmd_reg_cs and mi_pipe_wr and cmd_reset;
            ctl_rd_en2   <= ctl_rd_en;
        end if;
    end process;

    dly_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dly_reg <= std_logic_vector(to_unsigned(64, 32));
            elsif ((dly_reg_cs = '1') and (mi_pipe_wr = '1')) then
                dly_reg <= mi_pipe_dwr;
            end if;
        end if;
    end process;

    ctl_stop_dly <= dly_reg(log2(ITEMS)-1 downto 0);

    sel_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                sel_reg <= (others => '0');
            elsif ((sel_reg_cs = '1') and (mi_pipe_wr = '1')) then
                sel_reg <= mi_pipe_dwr;
            end if;
        end if;
    end process;

    cap_reg_sel <= sel_reg(log2(DWORDS)-1 downto 0);

    cap_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (ctl_rd_en2 = '1') then
                cap_reg <= (others => '0');
                cap_reg(DATA_WIDTH-1 downto 0) <= ctl_rd_data;
            end if;
        end if;
    end process;

    cap_reg_mux_i : entity work.GEN_MUX
    generic map(
        DATA_WIDTH => 32,
        MUX_WIDTH  => DWORDS
    )
    port map(
        DATA_IN  => cap_reg,
        SEL      => cap_reg_sel,
        DATA_OUT => cap_reg_mux
    );

    status_reg <= std_logic_vector(to_unsigned(ITEMS, 28)) & "000" & ctl_stop_reg;

    mi_drd_mux_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            case (mi_pipe_addr(7 downto 2)) is
                when "000000" => mi_pipe_drd <= status_reg; --0x00
                when "000001" => mi_pipe_drd <= dly_reg; --0x04
                when "000010" => mi_pipe_drd <= sel_reg; --0x08
                when "000011" => mi_pipe_drd <= cap_reg_mux; --0x0C
                when others   => mi_pipe_drd <= X"DEADCAFE";
            end case;
        end if;
    end process;

    mi_drdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                mi_pipe_drdy <= '0';
            else
                mi_pipe_drdy <= mi_pipe_rd;
            end if;
        end if;
    end process;

end architecture;
