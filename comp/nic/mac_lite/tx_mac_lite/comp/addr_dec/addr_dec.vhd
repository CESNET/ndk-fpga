-- addr_dec.vhd: TX MAC Lite MI32 Address decoder
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Michal Suchanek <xsucha12@stud.feec.vutbr.cz>
--            Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity TX_MAC_LITE_ADDR_DEC is
    generic(
        -- Is enabled CRC insertion in TX_MAC_LITE?
        CRC_INSERTION_EN : boolean := True;
        DEVICE           : string  := "STRATIX10"
    );
    port(
        -- CLOCK AND RESET
        CLK                             : in  std_logic;
        RESET                           : in  std_logic;
        -- MI32 INTERFACE (MI_CLK)
        MI_CLK                          : in  std_logic;
        MI_RESET                        : in  std_logic;
        MI_DWR                          : in  std_logic_vector(31 downto 0);
        MI_ADDR                         : in  std_logic_vector(31 downto 0);
        MI_RD                           : in  std_logic;
        MI_WR                           : in  std_logic;
        MI_BE                           : in  std_logic_vector(3 downto 0);
        MI_DRD                          : out std_logic_vector(31 downto 0);
        MI_ARDY                         : out std_logic;
        MI_DRDY                         : out std_logic;
        -- STATISTICS INPUTS INTERFACE (CLK)
        STAT_TOTAL_FRAMES               : in  std_logic_vector(63 downto 0);
        STAT_TOTAL_SENT_FRAMES          : in  std_logic_vector(63 downto 0);
        STAT_TOTAL_SENT_OCTECTS         : in  std_logic_vector(63 downto 0);
        STAT_TOTAL_DISCARDED_FRAMES     : in  std_logic_vector(63 downto 0);
        -- CONTROL OUTPUT INTERFACE (CLK)
        CTRL_STROBE_CNT                 : out std_logic;
        CTRL_RESET_CNT                  : out std_logic;
        CTRL_OBUF_EN                    : out std_logic
    );
end entity;

architecture FULL of TX_MAC_LITE_ADDR_DEC is

    -- Constants addresses
    constant ADDR_CNT_TOTAL_FRAMES_L    : std_logic_vector(7 downto 0) := X"00";
    constant ADDR_CNT_TOTAL_FRAMES_H    : std_logic_vector(7 downto 0) := X"10";
    constant ADDR_CNT_SENT_FRAMES_L     : std_logic_vector(7 downto 0) := X"0C";
    constant ADDR_CNT_SENT_FRAMES_H     : std_logic_vector(7 downto 0) := X"1C";
    constant ADDR_CNT_SENT_OCTECTS_L    : std_logic_vector(7 downto 0) := X"04";
    constant ADDR_CNT_SENT_OCTECTS_H    : std_logic_vector(7 downto 0) := X"14";
    constant ADDR_CNT_DISCARDS_FRAMES_L : std_logic_vector(7 downto 0) := X"08";
    constant ADDR_CNT_DISCARDS_FRAMES_H : std_logic_vector(7 downto 0) := X"18";
    constant ADDR_REG_OBUF_EN           : std_logic_vector(7 downto 0) := X"20";
    constant ADDR_REG_CTRL              : std_logic_vector(7 downto 0) := X"2C";
    constant ADDR_REG_STATUS            : std_logic_vector(7 downto 0) := X"30";

    -- OBUF commands
    constant OBUFCMD_STROBE_COUNTERS    : std_logic_vector(7 downto 0) := X"01";
    constant OBUFCMD_RESET_COUNTERS     : std_logic_vector(7 downto 0) := X"02";

    -- Ethernet speed code status
    constant ETH_SPEED_CODE             : std_logic_vector(2 downto 0) := "101";

    -- MI32 signals
    signal mi_s_dwr           : std_logic_vector(31 downto 0);
    signal mi_s_addr          : std_logic_vector(31 downto 0);
    signal mi_s_rd            : std_logic;
    signal mi_s_wr            : std_logic;
    signal mi_s_be            : std_logic_vector(3 downto 0);
    signal mi_s_drd           : std_logic_vector(31 downto 0);
    signal mi_s_ardy          : std_logic;
    signal mi_s_drdy          : std_logic;
    signal mi_s_active_reg    : std_logic;
    signal mi_s_drd_reg       : std_logic_vector(31 downto 0);
    signal mi_s_drdy_reg      : std_logic;

    -- MI32 registers select signals
    signal obuf_en_reg_sel    : std_logic;
    signal ctrl_regs_sel      : std_logic;
    signal status_reg_sel     : std_logic;

    -- MI32 registers write enable signals
    signal obuf_en_reg_we     : std_logic;
    signal ctrl_regs_we       : std_logic;
    signal status_reg_we      : std_logic;

    -- MI32 registers
    signal cmd_strobe_cnt     : std_logic;
    signal cmd_strobe_cnt_reg : std_logic;
    signal cmd_reset_cnt      : std_logic;
    signal cmd_reset_cnt_reg  : std_logic;
    signal obuf_en_reg        : std_logic;
    signal obuf_en_reg_32     : std_logic_vector(31 downto 0);
    signal status_disable_crc : std_logic;
    signal status_reg         : std_logic_vector(6 downto 0) := "1010000";
    signal status_reg_32      : std_logic_vector(31 downto 0);

begin

    -- =========================================================================
    --  MI32 ASYNC HANDSHAKE
    -- =========================================================================

    mi_async_i : entity work.MI_ASYNC
    generic map(
        DEVICE => DEVICE
    )
    port map(
        -- Master side
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
        -- Slave side
        CLK_S     => CLK,
        RESET_S   => RESET,
        MI_S_DWR  => mi_s_dwr,
        MI_S_ADDR => mi_s_addr,
        MI_S_RD   => mi_s_rd,
        MI_S_WR   => mi_s_wr,
        MI_S_BE   => mi_s_be,
        MI_S_DRD  => mi_s_drd_reg,
        MI_S_ARDY => mi_s_ardy,
        MI_S_DRDY => mi_s_drdy_reg
    );

    -- =========================================================================
    --  MI32 CONTROL LOGIC
    -- =========================================================================

    -- MI32 write control logic ------------------------------------------------

    reg_sel_p : process(mi_s_addr)
    begin
        case (mi_s_addr(7 downto 0)) is
            when ADDR_REG_OBUF_EN =>
                obuf_en_reg_sel <= '1';
                ctrl_regs_sel   <= '0';
                status_reg_sel  <= '0';
            when ADDR_REG_CTRL =>
                obuf_en_reg_sel <= '0';
                ctrl_regs_sel   <= '1';
                status_reg_sel  <= '0';
            when ADDR_REG_STATUS =>
                obuf_en_reg_sel <= '0';
                ctrl_regs_sel   <= '0';
                status_reg_sel  <= '1';
            when others =>
                obuf_en_reg_sel <= '0';
                ctrl_regs_sel   <= '0';
                status_reg_sel  <= '0';
        end case;
    end process;

    obuf_en_reg_we <= obuf_en_reg_sel and mi_s_wr and mi_s_active_reg;
    ctrl_regs_we   <= ctrl_regs_sel and mi_s_wr and mi_s_active_reg;
    status_reg_we  <= status_reg_sel and mi_s_wr and mi_s_active_reg;

    -- MI32 read control logic -------------------------------------------------

    status_disable_crc <= '1' when (CRC_INSERTION_EN = False) else '0';

    obuf_en_reg_32 <= (31 downto 1 => '0') & obuf_en_reg;
    status_reg_32  <= (31 downto 7 => '0') & ETH_SPEED_CODE & "00" & status_disable_crc & obuf_en_reg;

    mi_s_drd_mux_p : process(all)
    begin
        case (mi_s_addr(7 downto 0)) is
            when ADDR_CNT_TOTAL_FRAMES_L =>
                mi_s_drd <= STAT_TOTAL_FRAMES(31 downto 0);
            when ADDR_CNT_TOTAL_FRAMES_H =>
                mi_s_drd <= STAT_TOTAL_FRAMES(63 downto 32);
            when ADDR_CNT_SENT_FRAMES_L =>
                mi_s_drd <= STAT_TOTAL_SENT_FRAMES(31 downto 0);
            when ADDR_CNT_SENT_FRAMES_H =>
                mi_s_drd <= STAT_TOTAL_SENT_FRAMES(63 downto 32);
            when ADDR_CNT_SENT_OCTECTS_L =>
                mi_s_drd <= STAT_TOTAL_SENT_OCTECTS(31 downto 0);
            when ADDR_CNT_SENT_OCTECTS_H =>
                mi_s_drd <= STAT_TOTAL_SENT_OCTECTS(63 downto 32);
            when ADDR_CNT_DISCARDS_FRAMES_L =>
                mi_s_drd <= STAT_TOTAL_DISCARDED_FRAMES(31 downto 0);
            when ADDR_CNT_DISCARDS_FRAMES_H =>
                mi_s_drd <= STAT_TOTAL_DISCARDED_FRAMES(63 downto 32);
            when ADDR_REG_OBUF_EN =>
                mi_s_drd <= obuf_en_reg_32;
            when ADDR_REG_STATUS =>
                mi_s_drd <= status_reg_32;
            -- undefined address
            when others =>
                mi_s_drd <= X"DEADCAFE";
        end case;
    end process;

    -- MI32 common control logic -----------------------------------------------

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (mi_s_rd = '1' or mi_s_wr = '1') then
                mi_s_active_reg <= '1';
            end if;
            if (mi_s_active_reg = '1') then
                mi_s_active_reg <= '0';
            end if;
            if (RESET = '1') then
                mi_s_active_reg <= '0';
            end if;
        end if;
    end process;

    mi_s_ardy <= mi_s_active_reg;
    mi_s_drdy <= mi_s_rd and mi_s_active_reg;

    mi_s_drdy_reg_p : process(CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                mi_s_drdy_reg <= '0';
            else
                mi_s_drdy_reg <= mi_s_drdy;
            end if;
        end if;
    end process;

    mi_s_drd_reg_p : process(CLK)
    begin
        if rising_edge(CLK) then
            mi_s_drd_reg <= mi_s_drd;
        end if;
    end process;

    -- =========================================================================
    --  COMMAND AND ENABLE REGISTERS
    -- =========================================================================

    cmd_strobe_cnt <= '1' when ((mi_s_dwr(7 downto 0) = OBUFCMD_STROBE_COUNTERS) and (ctrl_regs_we = '1')) else '0';
    cmd_reset_cnt  <= '1' when ((mi_s_dwr(7 downto 0) = OBUFCMD_RESET_COUNTERS)  and (ctrl_regs_we = '1')) else '0';

    cmd_regs_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            cmd_strobe_cnt_reg <= cmd_strobe_cnt;
            cmd_reset_cnt_reg  <= cmd_reset_cnt or RESET;
        end if;
    end process;

    obuf_en_reg_p : process(CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                obuf_en_reg <= '0';
            elsif (obuf_en_reg_we = '1') then
                obuf_en_reg <= mi_s_dwr(0);
            end if;
        end if;
    end process;

    -- =========================================================================
    --  OUTPUTS ASSIGMENTS
    -- =========================================================================

    CTRL_STROBE_CNT <= cmd_strobe_cnt_reg;
    CTRL_RESET_CNT  <= cmd_reset_cnt_reg;
    CTRL_OBUF_EN    <= obuf_en_reg;

end architecture;
