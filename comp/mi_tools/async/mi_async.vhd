-- mi_async.vhd: Component for transmit MI data between two clocks domains
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- The MI_ASYNC implements the MI bus transition between two clock domains.
-- Asynchronous FIFO memory is used to implement the cross-domain crossing.
-- The MI_ASYNC component also contains logic that can ensure the correct
-- behavior of the MI bus in the event of an unexpected reset in only one clock
-- domain (see RESET_LOGIC generic).
entity MI_ASYNC is
    generic(
        -- Data word width in bits, must be power of 2.
        DATA_WIDTH  : natural := 32;
        -- Address word width in bits.
        ADDR_WIDTH  : natural := 32;
        -- Meta word width in bits.
        META_WIDTH  : natural := 2;
        -- Select memory implementation. Options: "LUT" or "BRAM"
        RAM_TYPE    : string  := "LUT";
        -- RESET_LOGIC provides additional logic for safe asynchronous reset of the component
        -- when one or both of the sides are in reset state, without violating MI protocol
        RESET_LOGIC : boolean := true;
        -- The DEVICE parameter allows the correct selection of the RAM
        -- implementation according to the FPGA used.
        DEVICE      : string  := "ULTRASCALE"
    );
    port(
        -- Master interface: Clock
        CLK_M     : in  std_logic;
        -- Master interface: Reset
        RESET_M   : in  std_logic;
        -- Master interface: MI Write Data
        MI_M_DWR  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Master interface: MI Write Metadata
        MI_M_MWR  : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
        -- Master interface: MI Address
        MI_M_ADDR : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
        -- Master interface: MI Read Request
        MI_M_RD   : in  std_logic;
        -- Master interface: MI Write Request
        MI_M_WR   : in  std_logic;
        -- Master interface: Byte Enable
        MI_M_BE   : in  std_logic_vector((DATA_WIDTH/8)-1 downto 0);
        -- Master interface: MI Read Data
        MI_M_DRD  : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Master interface: MI Address Ready
        MI_M_ARDY : out std_logic;
        -- Master interface: MI Read Data Ready
        MI_M_DRDY : out std_logic;

        -- Slave interface: Clock
        CLK_S     : in  std_logic;
        -- Slave interface: Reset
        RESET_S   : in  std_logic;
        -- Slave interface: MI Write Data
        MI_S_DWR  : out std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Slave interface: MI Write Metadata
        MI_S_MWR  : out std_logic_vector(META_WIDTH-1 downto 0);
        -- Slave interface: MI Address
        MI_S_ADDR : out std_logic_vector(ADDR_WIDTH-1 downto 0);
        -- Slave interface: MI Read Request
        MI_S_RD   : out std_logic;
        -- Slave interface: MI Write Request
        MI_S_WR   : out std_logic;
        -- Slave interface: Byte Enable
        MI_S_BE   : out std_logic_vector((DATA_WIDTH/8)-1 downto 0);
        -- Slave interface: MI Read Data
        MI_S_DRD  : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        -- Slave interface: MI Address Ready
        MI_S_ARDY : in  std_logic;
        -- Slave interface: MI Read Data Ready
        MI_S_DRDY : in  std_logic
    );
end entity;

architecture FULL of MI_ASYNC is

    constant FIFO_ITEMS    : natural := 16;
    constant FIFO_IN_WIDTH : natural := META_WIDTH+ADDR_WIDTH+DATA_WIDTH+(DATA_WIDTH/8)+1;
    constant RESET_MSG     : unsigned(32-1 downto 0) := x"DEADFEED";

    signal fifo_in_di     : std_logic_vector(FIFO_IN_WIDTH-1 downto 0);
    signal fifo_in_wr     : std_logic;
    signal fifo_in_full   : std_logic;
    signal fifo_in_do     : std_logic_vector(FIFO_IN_WIDTH-1 downto 0);
    signal fifo_in_rd     : std_logic;
    signal fifo_in_empty  : std_logic;
    signal fifo_out_empty : std_logic;
    signal fifo_out_do    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal m_drd_rdy      : std_logic;

    signal drdy_req       : std_logic;
    signal drdy_status    : unsigned(log2(FIFO_ITEMS+1)-1 downto 0) := (others => '0');
    signal drdy_rdy       : std_logic;

    type reset_state is (NO_RESET, MASTER_RESET, SLAVE_RESET, COMP_RESET);
    signal p_state        : reset_state := NO_RESET;
    signal n_state        : reset_state;
    signal reset_s_sync   : std_logic_vector(1-1 downto 0);
    signal no_reset_sig   : std_logic;

begin

    -----------------------------------------------------------------------------
    -- CROSS DOMAIN CROSSING OF MI REQUEST
    -----------------------------------------------------------------------------

    fifo_in_di <= MI_M_MWR & MI_M_DWR & MI_M_ADDR & MI_M_BE & MI_M_WR;
    fifo_in_wr <= (MI_M_WR or (MI_M_RD and drdy_rdy)) and (not fifo_in_full) and no_reset_sig;
    MI_M_ARDY  <= fifo_in_wr;

    fifo_in_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => FIFO_IN_WIDTH,
        ITEMS      => FIFO_ITEMS,
        RAM_TYPE   => RAM_TYPE,
        FWFT_MODE  => True,
        OUTPUT_REG => True,
        DEVICE     => DEVICE
    )
    port map(
        WR_CLK    => CLK_M,
        WR_RST    => reset_s_sync(0),
        WR_DATA   => fifo_in_di,
        WR_EN     => fifo_in_wr,
        WR_FULL   => fifo_in_full,
        WR_AFULL  => open,
        WR_STATUS => open,

        RD_CLK    => CLK_S,
        RD_RST    => RESET_S,
        RD_DATA   => fifo_in_do,
        RD_EN     => fifo_in_rd,
        RD_EMPTY  => fifo_in_empty,
        RD_AEMPTY => open,
        RD_STATUS => open
    );

    MI_S_WR    <= (not fifo_in_empty) and fifo_in_do(0);
    MI_S_RD    <= (not fifo_in_empty) and (not fifo_in_do(0));
    MI_S_BE    <= fifo_in_do((DATA_WIDTH/8)+1-1 downto 1);
    MI_S_ADDR  <= fifo_in_do(ADDR_WIDTH+(DATA_WIDTH/8)+1-1 downto (DATA_WIDTH/8)+1);
    MI_S_DWR   <= fifo_in_do(DATA_WIDTH+ADDR_WIDTH+(DATA_WIDTH/8)+1-1 downto ADDR_WIDTH+(DATA_WIDTH/8)+1);
    MI_S_MWR   <= fifo_in_do(FIFO_IN_WIDTH-1 downto DATA_WIDTH+ADDR_WIDTH+(DATA_WIDTH/8)+1);
    fifo_in_rd <= (not fifo_in_empty) and MI_S_ARDY;

    -----------------------------------------------------------------------------
    -- CROSS DOMAIN CROSSING OF MI RESPONSE
    -----------------------------------------------------------------------------

    fifo_out_i : entity work.ASFIFOX
    generic map(
        DATA_WIDTH => DATA_WIDTH,
        ITEMS      => FIFO_ITEMS,
        RAM_TYPE   => RAM_TYPE,
        FWFT_MODE  => False,
        OUTPUT_REG => True,
        DEVICE     => DEVICE
    )
    port map(
        WR_CLK    => CLK_S,
        WR_RST    => RESET_S,
        WR_DATA   => MI_S_DRD,
        WR_EN     => MI_S_DRDY,
        WR_FULL   => open, -- Cannot happen
        WR_AFULL  => open,
        WR_STATUS => open,

        RD_CLK    => CLK_M,
        RD_RST    => reset_s_sync(0),
        RD_DATA   => fifo_out_do,
        RD_EN     => '1',
        RD_EMPTY  => fifo_out_empty,
        RD_AEMPTY => open,
        RD_STATUS => open
    );

    m_drd_rdy <= '1' when ((fifo_out_empty = '0' and no_reset_sig = '1') or (p_state = SLAVE_RESET and drdy_status /= 0)) else '0';

    mi_m_drd_reg_p : process(CLK_M)
    begin
        if rising_edge(CLK_M) then
            if (p_state = SLAVE_RESET) then
                MI_M_DRD <= std_logic_vector(resize_right(RESET_MSG, DATA_WIDTH));
            else
                MI_M_DRD <= fifo_out_do;
            end if;
            MI_M_DRDY <= m_drd_rdy;
        end if;
    end process;


    -----------------------------------------------------------------------------
    -- STATUS COUNTER OF MI READ REQUESTS IN PROCESSING
    -----------------------------------------------------------------------------
    -- prevents overfull of the output FIFO

    drdy_req <= (MI_M_RD and drdy_rdy) and (not fifo_in_full) and no_reset_sig;

    process (CLK_M)
    begin
        if (rising_edge(CLK_M)) then
            if (p_state = COMP_RESET or (RESET_M = '1' and not RESET_LOGIC)) then
                drdy_status <= (others => '0');
            elsif (fifo_out_empty = '1' and drdy_req = '1') then -- only read request
                drdy_status <= drdy_status + 1;
            elsif ((fifo_out_empty = '0' and drdy_req = '0') or (p_state = SLAVE_RESET and drdy_status /= 0)) then -- only read response
                drdy_status <= drdy_status - 1;
            end if;
        end if;
    end process;

    drdy_rdy <= '1' when (drdy_status < FIFO_ITEMS) else '0';

    -----------------------------------------------------------------------------
    -- RESET FSM
    -----------------------------------------------------------------------------
    -- logic for correct reset of MI_ASYNC

    sync_reset_s_i : entity work.ASYNC_RESET
    generic map(
        TWO_REG   => False,
        OUT_REG   => False
    )
    port map(
        CLK       => CLK_M,
        ASYNC_RST => RESET_S,
        OUT_RST   => reset_s_sync
    );

    -- INFO: obsolete, generates warning in simulation
    --no_reset_logic_g : if not RESET_LOGIC generate
    --    p_state <= NO_RESET;
    --end generate;

    reset_logic_g : if RESET_LOGIC generate
        fsm_state_p : process (CLK_M)
        begin
            if (rising_edge(CLK_M)) then
                p_state <= n_state;
            end if;
        end process;

        fsm_n_state_logic_p : process (p_state, RESET_M, reset_s_sync, drdy_status)
        begin
            n_state <= NO_RESET;
            case p_state is
                when NO_RESET =>
                    if (RESET_M = '1' and reset_s_sync(0) = '1') then
                        n_state <= COMP_RESET;
                    elsif (RESET_M = '1') then
                        n_state <= MASTER_RESET;
                    elsif (reset_s_sync(0) = '1') then
                        n_state <= SLAVE_RESET;
                    end if;
                when COMP_RESET =>
                    n_state <= COMP_RESET;
                    if (RESET_M = '0' and reset_s_sync(0) = '0') then
                        n_state <= NO_RESET;
                    end if;
                when MASTER_RESET =>
                    n_state <= MASTER_RESET;
                    if (reset_s_sync(0) = '1') then
                        n_state <= COMP_RESET;
                    elsif (RESET_M = '0' and drdy_status = 0) then
                        n_state <= NO_RESET;
                    end if;
                when SLAVE_RESET =>
                    n_state <= SLAVE_RESET;
                    if (RESET_M = '1') then
                        n_state <= COMP_RESET;
                    elsif (reset_s_sync(0) = '0' and drdy_status = 0) then
                        n_state <= NO_RESET;
                    end if;
                when others =>
                    null;
            end case;
        end process;
    end generate;

    no_reset_sig <= '1' when (p_state = NO_RESET) else '0';

end architecture;

