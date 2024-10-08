-- Modules.tcl: Components include script
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- Descritpion: Through this component it is possible to send MI transactions indirectly to one or more output interfaces.
--              That means you have to set the parameters of the MI transaction (by sending Write requests) to a set of registers,
--              which are also accessed by MI.

-- Warning: Check the status bit before sending each request to avoid possible errors.
--          The LSB of the Status register indicates business of the component - if set high, the component is busy and you must
--          not send any requests (except for reading the Status register).
--          Also, reading DRD register without sending a read request first may result in reading old/invalid data.

entity MI_INDIRECT_ACCESS is
    generic(
	-- Width of MI data
        DATA_WIDTH        : natural := 32;
	-- Width of MI address
        ADDR_WIDTH        : natural := 32;

	-- Number of output interfaces
        OUTPUT_INTERFACES : natural := 3
    );
    port(
        -- =================
        -- Common interface
        -- =================

        CLK         : in std_logic;
        RESET       : in std_logic;

        -- ==================
        -- Input MI interface
        -- ==================

        RX_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        RX_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_WR       : in  std_logic;
        RX_RD       : in  std_logic;
        RX_ARDY     : out std_logic;
        RX_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_DRDY     : out std_logic;

        -- ===================
        -- Output MI interface
        -- ===================

        TX_ADDR     : out slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_DWR      : out slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_WR       : out std_logic_vector(OUTPUT_INTERFACES-1 downto 0);
        TX_RD       : out std_logic_vector(OUTPUT_INTERFACES-1 downto 0);
        TX_ARDY     : in  std_logic_vector(OUTPUT_INTERFACES-1 downto 0);
        TX_DRD      : in  slv_array_t     (OUTPUT_INTERFACES-1 downto 0)(DATA_WIDTH-1 downto 0);
        TX_DRDY     : in  std_logic_vector(OUTPUT_INTERFACES-1 downto 0)
    );
end entity;

architecture FULL of MI_INDIRECT_ACCESS is

    -- ====================================================================
    --                              CONSTANTS
    -- ====================================================================

    -- 2 for MI32
    constant UNNECESSARY_BITS : natural := log2(DATA_WIDTH/8);

    -- Write, Read;  can be expanded if necessary
    constant COMMANDS         : natural := 2;
    -- Busy; can be expanded if necessary
    constant STATUSES         : natural := 1;

    -- ==========
    -- Addresses
    -- ==========

    -- Interface register - set this register to choose output interface
    -- 0x00
    constant INF_REG_ADDR             : std_logic_vector(7 downto UNNECESSARY_BITS) := "000000";
    -- Address register - this register stores the address of the request that will be sent to desired output interface
    -- 0x04
    constant ADDR_REG_ADDR            : std_logic_vector(7 downto UNNECESSARY_BITS) := "000001";
    -- Write data register - this register stores the data of Write request that will come from desired output interface
    -- 0x08
    constant DWR_REG_ADDR             : std_logic_vector(7 downto UNNECESSARY_BITS) := "000010";
    -- Read data register - this register stores the data of Read request that will come from desired output interface
    -- 0x0C
    constant DRD_REG_ADDR             : std_logic_vector(7 downto UNNECESSARY_BITS) := "000011";
    -- Command register (cmd_reg(0) = Write, cmd_reg(1) = Read) - after asserting WR or RD, the request will be sent
    -- 0x10
    constant COMMAND_REG_ADDR         : std_logic_vector(7 downto UNNECESSARY_BITS) := "000100";
    -- Status register (stat_reg(0) = Busy)
    -- 0x14
    constant STATUS_REG_ADDR          : std_logic_vector(7 downto UNNECESSARY_BITS) := "000101";

    -- ====================================================================
    --                               SIGNALS
    -- ====================================================================
    signal inf_reg           : natural;
    signal addr_reg          : std_logic_vector(ADDR_WIDTH-1 downto 0);
    signal dwr_reg           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal drd_reg           : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal cmd               : std_logic_vector(COMMANDS  -1 downto 0);
    signal cmd_reg           : std_logic_vector(COMMANDS  -1 downto 0);
    signal stat_reg          : std_logic_vector(STATUSES  -1 downto 0);

    -- state signals for FSM
    type state is (IDLE, WR, RD, DRD);
    signal present_st        : state := IDLE;
    signal next_st           : state := IDLE;

begin

    -- Writing ------------------------------------------------------------
    cmd <= RX_DWR(COMMANDS-1 downto 0) when ((RX_WR = '1') and
                                             (RX_ADDR(7 downto UNNECESSARY_BITS) = COMMAND_REG_ADDR))
      else (others => '0');

    write_regs_p : process (CLK)
    begin
        if rising_edge(CLK) then

            if (RX_WR = '1') then
                case RX_ADDR(7 downto UNNECESSARY_BITS) is
                    when INF_REG_ADDR     => inf_reg  <= to_integer(unsigned(RX_DWR(log2(OUTPUT_INTERFACES)-1 downto 0)));
                    when ADDR_REG_ADDR    => addr_reg <= RX_DWR;
                    when DWR_REG_ADDR     => dwr_reg  <= RX_DWR;
                    when others           => null;
                end case;
            end if;

            if (stat_reg(0) = '0') then
                cmd_reg <= cmd;
            end if;

            if (RESET = '1') then
                inf_reg <= 0;
            end if;

        end if;
    end process;

    -- ------------------------------------------------------------
    -- FSM (IDLE - can read from or write to regs, WR - write req sent out, RD - read req sent out, DRD - reading in progress)
    -- ------------------------------------------------------------
    present_state_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            present_st <= next_st;
            if (RESET = '1') then
                present_st <= IDLE;
            end if;
        end if;
    end process;

    next_state_p : process (all)
    begin
        case present_st is

            when IDLE =>
                -- send WR request
                if (cmd(0) = '1') then
                    next_st <= WR;
                -- send RD request
                elsif (cmd(1) = '1') then
                    next_st <= RD;
                -- Error state - WR and RD = '1'
                elsif (and cmd) then
                    next_st <= IDLE;
                    assert false
                        report "Read and Write requests at the same time !!"
                        severity failure;
                else
                    next_st <= IDLE;
                end if;

            when WR =>
                if (TX_ARDY(inf_reg) = '1') then
                    next_st <= IDLE;
                else
                    next_st <= WR;
                end if;

            when RD =>
                if (TX_ARDY(inf_reg) = '1') and (TX_DRDY(inf_reg) = '1') then
                    next_st <= IDLE;
                elsif (TX_ARDY(inf_reg) = '1') then
                    next_st <= DRD;
                else
                    next_st <= RD;
                end if;

            when DRD =>
                if (TX_DRDY(inf_reg) = '1') then
                    next_st <= IDLE;
                else
                    next_st <= DRD;
                end if;

            when others =>
                next_st <= IDLE;
        end case;
    end process;

    -- Control ------------------------------------------------------------
    output_logic_p : process (all)
    begin
        TX_WR <= (others => '0');
        TX_RD <= (others => '0');
        case present_st is
            when IDLE   => stat_reg(0) <= '0';

            when WR     => stat_reg(0)    <= '1';
                           TX_WR(inf_reg) <= cmd_reg(0);

            when RD     => stat_reg(0)    <= '1';
                           TX_RD(inf_reg) <= cmd_reg(1);

            when DRD    => stat_reg(0) <= '1';

            when others => stat_reg(0) <= '1';
        end case;
    end process;

    TX_ADDR <= (others => addr_reg);
    TX_DWR  <= (others => dwr_reg);

    drd_reg_p: process(CLK)
    begin
        if rising_edge(CLK) then
            if (TX_DRDY(inf_reg) = '1') then
                drd_reg <= TX_DRD(inf_reg);
            end if;
        end if;
    end process;

    RX_ARDY <= RX_WR or RX_RD;

    -- Reading ------------------------------------------------------------
    read_regs_p : process (CLK)
    begin
        if rising_edge(CLK) then
            RX_DRDY <= RX_RD;
            case RX_ADDR(7 downto UNNECESSARY_BITS) is
                when INF_REG_ADDR     => RX_DRD <= std_logic_vector(to_unsigned(inf_reg, DATA_WIDTH));
                when ADDR_REG_ADDR    => RX_DRD <= std_logic_vector(resize(unsigned(addr_reg), DATA_WIDTH));
                when DWR_REG_ADDR     => RX_DRD <= dwr_reg;
                when DRD_REG_ADDR     => RX_DRD <= drd_reg;
                when COMMAND_REG_ADDR => RX_DRD <= std_logic_vector(resize(unsigned(cmd_reg), DATA_WIDTH));
                when STATUS_REG_ADDR  => RX_DRD <= std_logic_vector(resize(unsigned(stat_reg), DATA_WIDTH));
                when others           => RX_DRD <= X"DEADCAFE";
            end case;
        end if;
    end process;

end architecture;

