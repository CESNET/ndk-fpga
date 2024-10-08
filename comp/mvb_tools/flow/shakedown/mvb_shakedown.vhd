-- mvb_shakedown.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal  <cabal@cesnet.cz>
--            Oliver Gurka <oliver.gurka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Converts ``RX_ITEMS`` item input MVB to ``TX_ITEMS`` amount of single item MVB interfaces.
-- Items can be read independetly and in order (out of order is not tested, UVM verification needed).
entity MVB_SHAKEDOWN is
    generic(
        -- RX MVB item count
        RX_ITEMS            : natural := 4;
        -- TX MVB independent interfaces count (can be merged to one MVB with MERGE component)
        TX_ITEMS            : natural := 1;
        -- Data item width
        ITEM_WIDTH          : natural := 128;
        -- Shake ports, when 1, ``RX_ITEMS`` must be read from TX interface to accept next transaction
        -- on RX MVB. When 2, ``RX_ITEMS/2`` must be read, etc. Scale this number carefully, consumes
        -- lot of resources. When one needs value of 3, consider using ``MULTI_FIFOX`` for such use case.
        -- Ingored when using *MUX* implemetation.
        SHAKE_PORTS         : natural := 2; -- allowed values: 1, 2, 3
        -- If set to true and TX_ITEMS = 1, this component will be implemented as simple
        -- multiplexer and logic emulating shakedown. This implementation does not provide
        -- buffering and does not break existing logic loops between SRC and DST readies.
        USE_MUX_IMPL        : boolean := False;
        DEVICE              : string  := "AGILEX"
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        -- =====================================================================
        --  INPUT MVB INTERFACE
        -- =====================================================================
        RX_DATA    : in  std_logic_vector(RX_ITEMS*ITEM_WIDTH-1 downto 0);
        RX_VLD     : in  std_logic_vector(RX_ITEMS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        --  OUTPUT MULTI MVB INTERFACE
        -- =====================================================================
        -- Transmit data (one item per MVB)
        TX_DATA    : out std_logic_vector(TX_ITEMS*ITEM_WIDTH-1 downto 0);
        -- Item valid, can be interpreted as ``SRC_RDY``
        TX_VLD     : out std_logic_vector(TX_ITEMS-1 downto 0);
        -- Next item request, can be interpreted as ``DST_RDY``
        TX_NEXT    : in  std_logic_vector(TX_ITEMS-1 downto 0)
    );
end entity;

architecture FULL of MVB_SHAKEDOWN is

    -- ============================
    -- Unequal RX/TX ITEMS interface wrapper
    -- ============================

    constant ITEMS       : integer := max(RX_ITEMS,TX_ITEMS);
    signal eq_RX_DATA    : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal eq_RX_VLD     : std_logic_vector(ITEMS-1 downto 0);
    signal eq_TX_DATA    : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal eq_TX_VLD     : std_logic_vector(ITEMS-1 downto 0);
    signal eq_TX_NEXT    : std_logic_vector(ITEMS-1 downto 0);

    -- ============================

    signal s_rx_dst_rdy             : std_logic;
    signal s_rx_vld_reg             : std_logic_vector(ITEMS-1 downto 0);
    signal s_rx_data_reg            : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);

    signal s_sh_din                 : std_logic_vector(SHAKE_PORTS*ITEMS*ITEM_WIDTH-1 downto 0);
    signal s_sh_din_vld             : std_logic_vector(SHAKE_PORTS*ITEMS-1 downto 0);

    signal s_sh_dout                : std_logic_vector(SHAKE_PORTS*ITEMS*ITEM_WIDTH-1 downto 0);
    signal s_sh_dout_vld            : std_logic_vector(SHAKE_PORTS*ITEMS-1 downto 0);

    signal s_sh_dout_reg            : std_logic_vector(SHAKE_PORTS*ITEMS*ITEM_WIDTH-1 downto 0);
    signal s_sh_dout_vld_reg        : std_logic_vector(SHAKE_PORTS*ITEMS-1 downto 0);
    signal s_sh_dout_vld_reg_masked : std_logic_vector(SHAKE_PORTS*ITEMS-1 downto 0);

    signal s_tx_data_reg            : std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
    signal s_tx_vld_reg             : std_logic_vector(ITEMS-1 downto 0);

    -- =====================================
    -- Shift register implemetation signals
    -- =====================================

    signal item_sent_reg        : std_logic_vector(RX_ITEMS - 1 downto 0);
    signal item_sent_reg_set    : std_logic_vector(RX_ITEMS - 1 downto 0);
    signal item_sent_reg_reset  : std_logic_vector(RX_ITEMS - 1 downto 0);

    signal item_vld_vec         : std_logic_vector(RX_ITEMS - 1 downto 0);
    signal items_left           : std_logic_vector(log2(RX_ITEMS + 1) - 1 downto 0);
    signal no_items_left        : std_logic;
    signal one_item_left        : std_logic;

    signal first_one_src_rdy    : std_logic_vector(RX_ITEMS - 1 downto 0);
    signal enc_if_addr          : std_logic_vector(max(log2(RX_ITEMS), 1) - 1 downto 0);

    signal mux_tx_data          : std_logic_vector(ITEM_WIDTH - 1 downto 0);
    signal mux_tx_vld           : std_logic_vector(0 downto 0);
begin
    mvb_shakedown_g : if not (TX_ITEMS = 1 and USE_MUX_IMPL) generate
        -- ============================
        -- Unequal RX/TX ITEMS interface wrapper
        -- ============================

        eq_RX_DATA <= std_logic_vector(resize(unsigned(RX_DATA),ITEMS*ITEM_WIDTH));
        eq_RX_VLD  <= std_logic_vector(resize(unsigned(RX_VLD),ITEMS));

        TX_DATA    <= std_logic_vector(resize(unsigned(eq_TX_DATA),TX_ITEMS*ITEM_WIDTH));
        TX_VLD     <= std_logic_vector(resize(unsigned(eq_TX_VLD),TX_ITEMS));
        eq_TX_NEXT <= std_logic_vector(resize(unsigned(TX_NEXT),ITEMS));

        -- ============================

        RX_DST_RDY <= s_rx_dst_rdy;

        -- =========================================================================
        --  INPUT REGISTERS
        -- =========================================================================

        in_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (s_rx_dst_rdy = '1') then
                    s_rx_data_reg <= eq_RX_DATA;
                end if;
            end if;
        end process;

        in_vld_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_rx_vld_reg <= (others => '0');
                elsif (s_rx_dst_rdy = '1') then
                    s_rx_vld_reg <= eq_RX_VLD and RX_SRC_RDY;
                end if;
            end if;
        end process;

        -- =========================================================================
        --  INPUT LOGIC
        -- =========================================================================

        sh_din_p : process (all)
        begin
            s_sh_din     <= s_sh_dout_reg;
            s_sh_din_vld <= s_sh_dout_vld_reg_masked;
            if (s_rx_dst_rdy = '1') then
                s_sh_din(SHAKE_PORTS*ITEMS*ITEM_WIDTH-1 downto (SHAKE_PORTS-1)*ITEMS*ITEM_WIDTH) <= s_rx_data_reg;
                s_sh_din_vld(SHAKE_PORTS*ITEMS-1 downto (SHAKE_PORTS-1)*ITEMS)                   <= s_rx_vld_reg;
            end if;
        end process;

        -- =========================================================================
        --  SHAKEDOWN MODULE
        -- =========================================================================

        shakedown_i : entity work.SHAKEDOWN
        generic map(
            INPUTS     => SHAKE_PORTS*ITEMS,
            OUTPUTS    => SHAKE_PORTS*ITEMS,
            DATA_WIDTH => ITEM_WIDTH
        )
        port map(
            CLK      => CLK,
            RESET    => RESET,

            DIN      => s_sh_din,
            DIN_VLD  => s_sh_din_vld,
            DOUT     => s_sh_dout,
            DOUT_VLD => s_sh_dout_vld
        );

        -- =========================================================================
        --  REGISTERS AND VALID MASKING
        -- =========================================================================

        sh_dout_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                s_sh_dout_reg <= s_sh_dout;
            end if;
        end process;

        sh_dout_vld_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_sh_dout_vld_reg <= (others => '0');
                else
                    s_sh_dout_vld_reg <= s_sh_dout_vld;
                end if;
            end if;
        end process;

        rx_dst_rdy_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    s_rx_dst_rdy <= '0';
                else
                    s_rx_dst_rdy <= not s_sh_dout_vld((SHAKE_PORTS-1)*ITEMS);
                end if;
            end if;
        end process;

        s_sh_dout_vld_reg_masked(SHAKE_PORTS*ITEMS-1 downto ITEMS) <= s_sh_dout_vld_reg(SHAKE_PORTS*ITEMS-1 downto ITEMS);
        s_sh_dout_vld_reg_masked(ITEMS-1 downto 0) <= s_sh_dout_vld_reg(ITEMS-1 downto 0) and (not eq_TX_NEXT);

        -- =========================================================================
        --  OUTPUT LOGIC
        -- =========================================================================

        eq_TX_DATA <= s_sh_dout_reg(ITEMS*ITEM_WIDTH-1 downto 0);
        eq_TX_VLD  <= s_sh_dout_vld_reg(ITEMS-1 downto 0);
    end generate;

    -- Implement effective N to 1 MVB shakedown
    mux_shakedown_g : if (TX_ITEMS = 1 and USE_MUX_IMPL) generate
        signal rx_data_int      : std_logic_vector(RX_ITEMS * ITEM_WIDTH - 1 downto 0);
        signal rx_vld_int       : std_logic_vector(RX_ITEMS - 1 downto 0);
        signal rx_src_rdy_int   : std_logic;
        signal rx_dst_rdy_int   : std_logic;
    begin
        RX_DST_RDY <= rx_dst_rdy_int;

        input_reg_p : process(CLK)
        begin
            if rising_edge(CLK) then
                if (rx_dst_rdy_int = '1') then
                    rx_data_int     <= RX_DATA;
                    rx_vld_int      <= RX_VLD;
                    rx_src_rdy_int  <= RX_SRC_RDY;
                end if;

                if (RESET = '1') then
                    rx_src_rdy_int <= '0';
                end if;
            end if;
        end process;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if RESET = '1' then
                    item_sent_reg <= (others => '1');
                else
                    for rx_it in 0 to RX_ITEMS - 1 loop
                        if item_sent_reg_set(rx_it) = '1' then
                            item_sent_reg(rx_it) <= '1';
                        elsif item_sent_reg_reset(rx_it) = '1' then
                            item_sent_reg(rx_it) <= '0';
                        end if;
                    end loop;
                end if;
            end if;
        end process;

        process (all)
        begin
            for i in 0 to RX_ITEMS - 1 loop
                item_vld_vec(i) <= item_sent_reg(i) and rx_vld_int(i) and rx_src_rdy_int;
            end loop;
        end process;

        no_items_left <= '1' when unsigned(items_left) = to_unsigned(0, log2(RX_ITEMS + 1)) else '0';
        one_item_left <= '1' when unsigned(items_left) = to_unsigned(1, log2(RX_ITEMS + 1)) else '0';

        rx_dst_rdy_int <= '1' when no_items_left = '1' or (one_item_left = '1' and TX_NEXT = "1") else '0';
        item_sent_reg_set <= (others => rx_dst_rdy_int);

        TX_VLD(0) <= not no_items_left and rx_src_rdy_int;

        -- TODO maybe replace with lookup table
        sum_one_i : entity work.SUM_ONE
        generic map (
            INPUT_WIDTH     => RX_ITEMS,
            OUTPUT_REG      => False
        ) port map (
            CLK             => CLK,
            RESET           => RESET,

            DIN             => item_vld_vec,
            DIN_MASK        => (others => '1'),
            DIN_VLD         => '1',

            DOUT            => items_left,
            DOUT_VLD        => open
        );

        first_one_i : entity work.FIRST_ONE
        generic map (
            DATA_WIDTH  => RX_ITEMS
        ) port map (
            DI          => item_vld_vec,
            DO          => first_one_src_rdy
        );

        enc_i       : entity work.GEN_ENC
        generic map (
            ITEMS       => RX_ITEMS,
            DEVICE      => DEVICE
        ) port map (
            DI          => first_one_src_rdy,
            ADDR        => enc_if_addr
        );

        data_mux_i : entity work.GEN_MUX
        generic map (
            DATA_WIDTH  => ITEM_WIDTH,
            MUX_WIDTH   => RX_ITEMS
        ) port map (
            DATA_IN     => rx_data_int,
            SEL         => enc_if_addr,
            DATA_OUT    => TX_DATA
        );

        drdy_demux_i : entity work.GEN_DEMUX
        generic map (
            DATA_WIDTH  => 1,
            DEMUX_WIDTH => RX_ITEMS,
            DEF_VALUE   => '0'
        ) port map (
            DATA_IN     => TX_NEXT,
            SEL         => enc_if_addr,
            DATA_OUT    => item_sent_reg_reset
        );
    end generate;
end architecture;
