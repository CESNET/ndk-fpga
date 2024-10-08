-- mi_reconf.vhd: MI Reconfigurator
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MI_RECONFIGURATOR is
generic(
    -- Input MI configuration
    RX_DATA_WIDTH : natural := 32;

    -- Output MI configuration
    TX_DATA_WIDTH : natural := 64;

    -- Common configuration
    ADDR_WIDTH    : natural := 32;
    META_WIDTH    : natural := 0
);
port(
    -- Common interface -----------------------------------------------------
    CLK         : in std_logic;
    RESET       : in std_logic;

    -- Input MI interface ---------------------------------------------------
    RX_DWR      : in  std_logic_vector(RX_DATA_WIDTH-1 downto 0);
    RX_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
    RX_ADDR     : in  std_logic_vector(ADDR_WIDTH-1 downto 0);
    RX_BE       : in  std_logic_vector(RX_DATA_WIDTH/8-1 downto 0);
    RX_RD       : in  std_logic;
    RX_WR       : in  std_logic;
    RX_ARDY     : out std_logic;
    RX_DRD      : out std_logic_vector(RX_DATA_WIDTH-1 downto 0);
    RX_DRDY     : out std_logic;

    -- Output MI interface --------------------------------------------------
    TX_DWR      : out std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    TX_MWR      : out std_logic_vector(META_WIDTH-1 downto 0);
    TX_ADDR     : out std_logic_vector(ADDR_WIDTH-1 downto 0);
    TX_BE       : out std_logic_vector(TX_DATA_WIDTH/8-1 downto 0);
    TX_RD       : out std_logic;
    TX_WR       : out std_logic;
    TX_ARDY     : in  std_logic;
    TX_DRD      : in  std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    TX_DRDY     : in  std_logic
);
end entity MI_RECONFIGURATOR;

architecture FULL of MI_RECONFIGURATOR is

    -- Resized interface
    signal RX_DWR_res  : std_logic_vector(TX_DATA_WIDTH-1 downto 0);
    signal RX_BE_res   : std_logic_vector(TX_DATA_WIDTH/8-1 downto 0);
    signal RX_DRD_res  : std_logic_vector(TX_DATA_WIDTH-1 downto 0);

    constant TX_PER_RX : natural := RX_DATA_WIDTH / TX_DATA_WIDTH;

    function gen_addr_inc return u_array_t is
        variable v : u_array_t(TX_PER_RX-1 downto 0)(ADDR_WIDTH-1 downto 0);
    begin
        for i in 0 to TX_PER_RX-1 loop
            v(i) := to_unsigned(i * TX_DATA_WIDTH / 8, ADDR_WIDTH);
        end loop;

        return v;
    end function;

    signal dwr_word_shift     : unsigned(log2(TX_DATA_WIDTH/8)-1 downto 0);
    signal reg_word_shift     : unsigned(log2(TX_DATA_WIDTH/8)-1 downto 0);
    signal reg_word_shift_vld : std_logic;
    signal drd_word_shift     : unsigned(log2(TX_DATA_WIDTH/8)-1 downto 0);

    signal RX_BE_arr : slv_array_t(TX_PER_RX-1 downto 0)(TX_DATA_WIDTH/8-1 downto 0);

    -- Request sending register
    signal reg_req_dwr  : slv_array_t     (TX_PER_RX-1 downto 0)(TX_DATA_WIDTH-1 downto 0);
    signal reg_req_mwr  : std_logic_vector(META_WIDTH-1 downto 0);
    signal reg_req_addr : unsigned        (ADDR_WIDTH-1 downto 0);
    signal reg_req_be   : slv_array_t     (TX_PER_RX-1 downto 0)(TX_DATA_WIDTH/8-1 downto 0);
    signal reg_req_rd   : std_logic;
    signal reg_req_wr   : std_logic;
    signal reg_req_we   : std_logic_vector(TX_PER_RX-1 downto 0); -- Word Enable
    signal reg_req_vld  : std_logic;

    signal req_part_sel : integer := 0;
    signal req_we_next  : std_logic_vector(TX_PER_RX-1 downto 0);

    constant req_addr_inc : u_array_t(TX_PER_RX-1 downto 0)(ADDR_WIDTH-1 downto 0) := gen_addr_inc;

    -- Read request order reg array
    signal ord_wr_ptr    : unsigned(log2(TX_PER_RX)-1 downto 0);
    signal ord_rd_ptr    : unsigned(log2(TX_PER_RX)-1 downto 0);

    signal ord_rd_nzero  : std_logic; -- Is '1' even after ord_rd_ptr overflows to 0

    signal ord_value     : u_array_t       (TX_PER_RX-1 downto 0)(log2(TX_PER_RX)-1 downto 0);
    signal ord_vld       : std_logic_vector(TX_PER_RX-1 downto 0);

    -- Read request response
    signal res_part_sel : integer := 0;
    signal res_waiting  : std_logic;
    signal reg_res_drd  : slv_array_t(TX_PER_RX-1 downto 0)(TX_DATA_WIDTH-1 downto 0) := (others => (others => '0'));

begin

    assert (RX_DATA_WIDTH/8*8 = RX_DATA_WIDTH)
        report "ERROR: MI Reconfigurator: RX_DATA_WIDTH (" & to_string(RX_DATA_WIDTH) & ") must be divisible by 8!" severity failure;
    assert (TX_DATA_WIDTH/8*8 = TX_DATA_WIDTH)
        report "ERROR: MI Reconfigurator: TX_DATA_WIDTH (" & to_string(TX_DATA_WIDTH) & ") must be divisible by 8!" severity failure;

    -- Resize input signals
    RX_DWR_res <= std_logic_vector(resize(unsigned(RX_DWR),TX_DATA_WIDTH  ));
    RX_BE_res  <= std_logic_vector(resize(unsigned(RX_BE ),TX_DATA_WIDTH/8));

    -- No data resizing
    data_res_none_gen : if (TX_DATA_WIDTH = RX_DATA_WIDTH) generate

        TX_DWR  <= RX_DWR;
        TX_MWR  <= RX_MWR;
        TX_ADDR <= RX_ADDR;
        TX_BE   <= RX_BE;
        TX_RD   <= RX_RD;
        TX_WR   <= RX_WR;
        RX_ARDY <= TX_ARDY;
        RX_DRD  <= TX_DRD;
        RX_DRDY <= TX_DRDY;

    end generate;

    -- Data resize up
    data_res_up_gen : if (TX_DATA_WIDTH > RX_DATA_WIDTH) generate

        TX_MWR  <= RX_MWR;
        TX_RD   <= RX_RD and (not reg_word_shift_vld); -- Don't propagate new read before the old one is finished
        TX_WR   <= RX_WR;
        RX_ARDY <= TX_ARDY;

        -- Take out part of request address as data shift
        dwr_word_shift <= resize_left(unsigned(RX_ADDR),log2(TX_DATA_WIDTH/8));

        -- Align signals to the new data width
        TX_ADDR <= std_logic_vector(round_down(unsigned(RX_ADDR),log2(TX_DATA_WIDTH/8)));
        TX_DWR  <= (RX_DWR_res rol to_integer(enlarge_right(dwr_word_shift,log2(8))));
        TX_BE   <= (RX_BE_res  rol to_integer(              dwr_word_shift         ));

        -- Word shift for read request response
        word_shift_reg : process (CLK)
        begin
            if (rising_edge(CLK)) then

                -- Store dwr_word shift for read response
                if (TX_RD = '1' and TX_ARDY = '1') then
                    reg_word_shift     <= dwr_word_shift;
                    reg_word_shift_vld <= '1';
                end if;

                -- Don't store / invalidate when a response comes
                if (TX_DRDY = '1') then
                    reg_word_shift_vld <= '0';
                end if;

                if (RESET='1') then
                    reg_word_shift_vld <= '0';
                end if;
            end if;
        end process;

        -- Select shift for response from register or asynchronously
        drd_word_shift <= reg_word_shift when reg_word_shift_vld = '1' else dwr_word_shift;

        -- Propagate read response
        RX_DRD_res <= (TX_DRD ror to_integer(enlarge_right(drd_word_shift,log2(8))));
        RX_DRD     <= std_logic_vector(resize(unsigned(RX_DRD_res),RX_DATA_WIDTH));

        RX_DRDY    <= TX_DRDY;

    end generate;

    -- Data resize down
    data_res_down_gen : if (TX_DATA_WIDTH < RX_DATA_WIDTH) generate

        RX_BE_arr <= slv_array_deser(RX_BE,TX_PER_RX);

        -- Request sending register
        req_reg : process (CLK)
        begin
            if (rising_edge(CLK)) then

                if (reg_req_vld = '1') then
                    if (TX_ARDY = '1') then
                        -- Update request
                        reg_req_dwr  <= reg_req_dwr;
                        reg_req_mwr  <= reg_req_mwr;
                        reg_req_addr <= reg_req_addr;
                        reg_req_be   <= reg_req_be;
                        reg_req_rd   <= reg_req_rd;
                        reg_req_wr   <= reg_req_wr;

                        -- Invalidate currently processed word
                        reg_req_we   <= req_we_next;

                        -- Invalide whole request when last part processed
                        reg_req_vld  <= (or req_we_next);
                    end if;
                else
                    -- Next request must wait for previous read response to be processed.
                    -- This prevents possible new write request from modifying the data
                    -- before they could be read.
                    if (res_waiting = '0') then
                        -- Load new request
                        reg_req_dwr  <= slv_array_deser(RX_DWR,TX_PER_RX);
                        reg_req_mwr  <= RX_MWR;
                        reg_req_addr <= unsigned(RX_ADDR);
                        reg_req_be   <= RX_BE_arr;
                        reg_req_rd   <= RX_RD;
                        reg_req_wr   <= RX_WR;

                        for i in 0 to TX_PER_RX-1 loop
                            reg_req_we(i) <= (or RX_BE_arr(i));
                        end loop;

                        reg_req_vld <= (or RX_BE) and (RX_RD or RX_WR);
                    end if;
                end if;

                if (RESET = '1') then
                    reg_req_vld <= '0';
                end if;
            end if;
        end process;

        req_part_sel_pr : process (reg_req_we)
        begin
            -- First 1 search
            req_part_sel <= 0;
            for i in 0 to TX_PER_RX-1 loop
                req_part_sel <= i;
                exit when (reg_req_we(i) = '1');
            end loop;
        end process;

        req_we_next_pr : process (all)
        begin
            req_we_next               <= reg_req_we;
            req_we_next(req_part_sel) <= '0';
        end process;

        -- Read request order reg array
        req_order_reg : process (all)
        begin
            if (rising_edge(CLK)) then

                -- Write req info
                if (TX_RD = '1' and TX_ARDY = '1') then
                    -- Store info about new request
                    ord_value(to_integer(ord_wr_ptr)) <= to_unsigned(req_part_sel,log2(TX_PER_RX));
                    ord_vld  (to_integer(ord_wr_ptr)) <= '1';

                    ord_wr_ptr <= ord_wr_ptr + 1;
                end if;

                -- Read req info
                if (TX_DRDY = '1') then
                    -- Read is destructive
                    -- Simultaneous write and read to the same position can
                    -- only happen when TX_DRDY is directly connected to TX_RD.
                    ord_vld(to_integer(ord_rd_ptr)) <= '0';

                    ord_rd_ptr   <= ord_rd_ptr + 1;
                    ord_rd_nzero <= '1';
                end if;

                -- Reset WR PTR for new request
                if (reg_req_vld = '0') then
                    ord_wr_ptr <= (others => '0');
                end if;

                -- Reset RD PTR for finished response
                if (res_waiting = '0') then
                    ord_rd_ptr   <= (others => '0');
                    ord_rd_nzero <= '0';
                end if;

                if (RESET = '1') then
                    ord_wr_ptr   <= (others => '0');
                    ord_rd_ptr   <= (others => '0');
                    ord_rd_nzero <= '0';

                    ord_vld      <= (others => '0');
                end if;
            end if;
        end process;

        -- Value in Order Register has 1 CLK latency
        -- Select req_part_sel directly in case TX_DRDY is directly connected to TX_RD
        res_part_sel <= to_integer(ord_value(to_integer(ord_rd_ptr)))
                   when ord_vld(to_integer(ord_rd_ptr)) = '1'
                   else req_part_sel;
        -- Detect response receiving retrospectively or directly
        res_waiting <= ord_vld(to_integer(ord_rd_ptr)) or (reg_req_vld and reg_req_rd);

        -- Read request response receiving register
        res_reg : process (CLK)
        begin
            if (rising_edge(CLK)) then

                -- Receive any read response
                -- Expect correct TX behavior
                if (TX_DRDY = '1') then
                    reg_res_drd(res_part_sel) <= TX_DRD;
                end if;

            end if;
        end process;

        TX_DWR  <= reg_req_dwr(req_part_sel);
        TX_MWR  <= reg_req_mwr;
        TX_ADDR <= std_logic_vector(reg_req_addr + req_addr_inc(req_part_sel));
        TX_BE   <= reg_req_be(req_part_sel);
        TX_RD   <= reg_req_rd and reg_req_vld;
        TX_WR   <= reg_req_wr and reg_req_vld;
        RX_ARDY <= RX_WR or RX_RD when reg_req_vld = '0' and res_waiting = '0' else '0';
        RX_DRD  <= slv_array_ser(reg_res_drd);
        -- Data is ready when we accepted at least 1 TX word and we are not waiting for more
        RX_DRDY <= '1' when ord_rd_nzero = '1' and res_waiting = '0' else '0';

    end generate;

end architecture;
