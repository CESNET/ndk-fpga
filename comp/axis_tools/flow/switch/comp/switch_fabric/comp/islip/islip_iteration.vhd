-- islip_iteration.vhd: ISLIP_ITERATION component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

entity ISLIP_ITERATION is
    generic (
        -- Number of input/output ports.
        NUM_PORTS : natural := 2;
        -- Number of requests per one input port queue.
        NUM_ITEMS : natural := 16;
        -- Target device.
        DEVICE    : string  := "AGILEX"
    );
    port (
        -- Clock and reset.
        CLK               : in  std_logic;
        RESET             : in  std_logic;

        -- Requests from input ports.
        RX_DEST_REQ_VEC   : in  slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
        -- Accepted requests from previous iteration.
        RX_DECISION_REG   : in  slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
        -- Sizes of individual requests from input ports.
        RX_DEST_REQ_SIZES : in  slv_array_2d_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0)(log2(NUM_ITEMS)+1-1 downto 0);
        -- Requests from input ports (registered value).
        TX_DEST_REQ_VEC   : out slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
        -- Accepted requests for next iteration.
        TX_DECISION_REG   : out slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0)
    );
end entity;

architecture FULL of ISLIP_ITERATION is
    signal s_ip_port_conn_info_arr  : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_op_port_conn_info_arr  : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_ip_port_unmatched      : std_logic_vector(NUM_PORTS-1 downto 0);
    signal s_op_port_unmatched      : std_logic_vector(NUM_PORTS-1 downto 0);

    signal s_dest_req_vec_arr       : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_req_vec_grant_arr      : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_grant_vec_arr          : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_accepted_grant_vec_arr : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_req_vec_accept_arr     : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_accept_vec_arr         : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);

    signal s_tx_decision_reg        : slv_array_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
begin

    port_conn_info_rows_g : for i in 0 to NUM_PORTS-1 generate
        s_ip_port_unmatched(i) <= nor s_ip_port_conn_info_arr(i);
        s_op_port_unmatched(i) <= nor s_op_port_conn_info_arr(i);
        port_conn_info_cols_g : for j in 0 to NUM_PORTS-1 generate
            s_ip_port_conn_info_arr(i)(j) <= RX_DECISION_REG(i)(j);
            s_op_port_conn_info_arr(i)(j) <= RX_DECISION_REG(j)(i);
        end generate;
    end generate;

    dest_req_vec_update_ip_g: for i in 0 to NUM_PORTS-1 generate
        dest_req_vec_update_op_g : for j in 0 to NUM_PORTS-1 generate
            signal s_req_up_to_date  : std_logic;
            signal s_ports_unmatched : std_logic;
        begin
            s_req_up_to_date         <= or RX_DEST_REQ_SIZES(i)(j);
            s_ports_unmatched        <= s_ip_port_unmatched(i) and s_op_port_unmatched(j);
            s_dest_req_vec_arr(i)(j) <= RX_DEST_REQ_VEC(i)(j) and s_ports_unmatched and s_req_up_to_date;
        end generate;
    end generate;

    arbiters_g : for i in 0 to NUM_PORTS-1 generate
        grant_arbiter_i : entity work.ARBITER
        generic map (
            NUM_PORTS => NUM_PORTS
        )
        port map (
            CLK          => CLK,
            RESET        => RESET,
            REQ_VECTOR   => s_req_vec_grant_arr(i),
            PRIORITY_INC => or s_accepted_grant_vec_arr(i),
            REQ_ACCEPT   => s_grant_vec_arr(i)
        );

        accept_arbiter_i : entity work.ARBITER
        generic map (
            NUM_PORTS => NUM_PORTS
        )
        port map (
            CLK          => CLK,
            RESET        => RESET,
            REQ_VECTOR   => s_req_vec_accept_arr(i),
            PRIORITY_INC => or s_accept_vec_arr(i),
            REQ_ACCEPT   => s_accept_vec_arr(i)
        );

        interconnect_g : for j in 0 to NUM_PORTS-1 generate
            s_req_vec_grant_arr(j)(i)      <= s_dest_req_vec_arr(i)(j);
            s_req_vec_accept_arr(j)(i)     <= s_grant_vec_arr(i)(j);
            s_accepted_grant_vec_arr(j)(i) <= s_accept_vec_arr(i)(j);
        end generate;
    end generate;

    tx_decision_reg_g : for i in 0 to NUM_PORTS-1 generate
        s_tx_decision_reg(i) <= RX_DECISION_REG(i) or s_accept_vec_arr(i);
    end generate;

    output_regs_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                TX_DEST_REQ_VEC <= (others => (others => '0'));
                TX_DECISION_REG <= (others => (others => '0'));
            else
                TX_DEST_REQ_VEC <= RX_DEST_REQ_VEC;
                TX_DECISION_REG <= s_tx_decision_reg;
            end if;
        end if;
    end process;

end architecture;
