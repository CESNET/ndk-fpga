-- mvb_aligner.vhd:
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MVB_ALIGNER is
    generic(
        ITEMS      : natural := 4;
        ITEM_WIDTH : natural := 32;
        DEVICE     : string  := "ULTRASCALE"
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
        RX_DATA    : in  std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        -- Position index of item in output word.
        RX_NEW_POS : in  std_logic_vector(ITEMS*log2(ITEMS)-1 downto 0);
        -- Item is last in output word.
        RX_NEW_LIW : in  std_logic_vector(ITEMS-1 downto 0);
        -- Fake item flag, when is high then output valid will be masked.
        RX_FAKE    : in  std_logic_vector(ITEMS-1 downto 0);
        RX_VLD     : in  std_logic_vector(ITEMS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        -- =====================================================================
        --  OUTPUT MVB INTERFACE
        -- =====================================================================
        TX_DATA    : out std_logic_vector(ITEMS*ITEM_WIDTH-1 downto 0);
        TX_VLD     : out std_logic_vector(ITEMS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB_ALIGNER is

    constant POS_WIDTH       : natural := log2(ITEMS);
    constant FIFO_DEPTH      : natural := 32;
    constant FIFO_PORT_WIDTH : natural := ITEM_WIDTH+POS_WIDTH+1+1;

    signal s_rx_data            : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_rx_new_pos         : slv_array_t(ITEMS-1 downto 0)(POS_WIDTH-1 downto 0);

    signal s_fifoxm_din         : slv_array_t(ITEMS-1 downto 0)(FIFO_PORT_WIDTH-1 downto 0);
    signal s_fifoxm_wr          : std_logic_vector(ITEMS-1 downto 0);
    signal s_fifoxm_full        : std_logic;
    signal s_fifoxm_dout_ser    : std_logic_vector(ITEMS*FIFO_PORT_WIDTH-1 downto 0);
    signal s_fifoxm_dout        : slv_array_t(ITEMS-1 downto 0)(FIFO_PORT_WIDTH-1 downto 0);
    signal s_fifoxm_rd          : std_logic_vector(ITEMS-1 downto 0);
    signal s_fifoxm_empty       : std_logic_vector(ITEMS-1 downto 0);

    signal s_fifoxm_mvb_data    : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_fifoxm_mvb_new_pos : slv_array_t(ITEMS-1 downto 0)(POS_WIDTH-1 downto 0);
    signal s_fifoxm_mvb_new_liw : std_logic_vector(ITEMS-1 downto 0);
    signal s_fifoxm_mvb_fake    : std_logic_vector(ITEMS-1 downto 0);
    signal s_fifoxm_mvb_vld     : std_logic_vector(ITEMS-1 downto 0);
    signal s_fifoxm_rd_req      : std_logic_vector(ITEMS-1 downto 0);

    signal s_aligner_rdy        : std_logic;
    signal s_new_mvb_vld        : std_logic_vector(ITEMS-1 downto 0);
    signal s_new_mvb_data       : slv_array_t(ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal s_new_mvb_dst_rdy    : std_logic;

begin

    s_rx_data    <= slv_array_downto_deser(RX_DATA,ITEMS,ITEM_WIDTH);
    s_rx_new_pos <= slv_array_downto_deser(RX_NEW_POS,ITEMS,POS_WIDTH);

    fifoxm_din_g : for i in 0 to ITEMS-1 generate
        s_fifoxm_din(i) <= s_rx_data(i) & s_rx_new_pos(i) & RX_NEW_LIW(i) & RX_FAKE(i);
    end generate;

    s_fifoxm_wr <= RX_VLD and RX_SRC_RDY;
    RX_DST_RDY  <= not s_fifoxm_full;

    fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH     => FIFO_PORT_WIDTH,
        ITEMS          => FIFO_DEPTH,
        WRITE_PORTS    => ITEMS,
        READ_PORTS     => ITEMS,
        RAM_TYPE       => "LUT",
        DEVICE         => DEVICE,
        SAFE_READ_MODE => false
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => slv_array_ser(s_fifoxm_din,ITEMS,FIFO_PORT_WIDTH),
        WR     => s_fifoxm_wr,
        FULL   => s_fifoxm_full,
        AFULL  => open,

        DO     => s_fifoxm_dout_ser,
        RD     => s_fifoxm_rd,
        EMPTY  => s_fifoxm_empty,
        AEMPTY => open
    );

    s_fifoxm_dout <= slv_array_downto_deser(s_fifoxm_dout_ser,ITEMS,FIFO_PORT_WIDTH);

    fifoxm_mvb_g : for i in 0 to ITEMS-1 generate
        s_fifoxm_mvb_data(i)    <= s_fifoxm_dout(i)(FIFO_PORT_WIDTH-1 downto 2+POS_WIDTH);
        s_fifoxm_mvb_new_pos(i) <= s_fifoxm_dout(i)(2+POS_WIDTH-1 downto 2);
        s_fifoxm_mvb_new_liw(i) <= s_fifoxm_dout(i)(1);
        s_fifoxm_mvb_fake(i)    <= s_fifoxm_dout(i)(0);
        s_fifoxm_mvb_vld(i)     <= not s_fifoxm_empty(i);
    end generate;

    fifoxm_rd_req_p : process (all)
    begin
        s_fifoxm_rd_req <= (others => '0');
        for i in 0 to ITEMS-1 loop
            s_fifoxm_rd_req(i) <= '1';
            if (s_fifoxm_mvb_new_liw(i) = '1') then
                exit;
            end if;
        end loop;
    end process;

    s_aligner_rdy <= or (s_fifoxm_mvb_vld and s_fifoxm_mvb_new_liw);
    s_fifoxm_rd   <= s_fifoxm_rd_req and s_aligner_rdy and s_new_mvb_dst_rdy;

    new_mvb_vld_demux_p : process (all)
    begin
        s_new_mvb_vld <= (others => '0');
        for i in 0 to ITEMS-1 loop
            if (s_aligner_rdy = '1' and s_fifoxm_mvb_fake(i) = '0') then
                s_new_mvb_vld(to_integer(unsigned(s_fifoxm_mvb_new_pos(i)))) <= '1';
            end if;
            if (s_fifoxm_mvb_new_liw(i) = '1') then
                exit;
            end if;
        end loop;
    end process;

    new_mvb_data_demux_p : process (all)
    begin
        s_new_mvb_data <= (others => s_fifoxm_mvb_data(0));
        for i in ITEMS-1 downto 0 loop
            s_new_mvb_data(to_integer(unsigned(s_fifoxm_mvb_new_pos(i)))) <= s_fifoxm_mvb_data(i);
        end loop;
    end process;

    -- =========================================================================
    --  MVB OUTPUT REGISTERS
    -- =========================================================================

    mvb_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (s_new_mvb_dst_rdy = '1') then
                TX_DATA <= slv_array_ser(s_new_mvb_data,ITEMS,ITEM_WIDTH);
                TX_VLD  <= s_new_mvb_vld;
            end if;
        end if;
    end process;

    mvb_srx_rdy_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TX_SRC_RDY <= '0';
            elsif (s_new_mvb_dst_rdy = '1') then
                TX_SRC_RDY <= or s_new_mvb_vld;
            end if;
        end if;
    end process;

    s_new_mvb_dst_rdy <= TX_DST_RDY or not TX_SRC_RDY;

end architecture;
