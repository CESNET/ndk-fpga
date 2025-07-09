-- islip.vhd: ISLIP component
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Tomas Hak <hak@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity ISLIP is
    generic (
        -- Number of input/output ports.
        NUM_PORTS      : natural := 2;
        -- Number of requests per one input port queue.
        NUM_ITEMS      : natural := 16;
        -- Number of iterations of iSLIP algorithm.
        NUM_ITERATIONS : natural := log2(NUM_PORTS)+1;
        -- Target device.
        DEVICE         : string  := "AGILEX"
    );
    port (
        -- Clock and reset.
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- Requests from input ports.
        DEST_REQ_VEC   : in  std_logic_vector(NUM_PORTS*NUM_PORTS-1 downto 0);
        -- Sizes of individual requests from input ports.
        DEST_REQ_SIZES : in  std_logic_vector(NUM_PORTS*NUM_PORTS*(log2(NUM_ITEMS)+1)-1 downto 0);

        -- IP/OP connections information.
        IP_CONN_VLD    : out std_logic_vector(NUM_PORTS-1 downto 0);
        IP_CONN_SEL    : out std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0);
        OP_CONN_VLD    : out std_logic_vector(NUM_PORTS-1 downto 0);
        OP_CONN_SEL    : out std_logic_vector(NUM_PORTS*log2(NUM_PORTS)-1 downto 0)
    );
end entity;

architecture FULL of ISLIP is
    signal s_dest_req_vec_2d_arr           : slv_array_2d_t(NUM_ITERATIONS+1-1 downto 0)(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_decision_reg_2d_arr           : slv_array_2d_t(NUM_ITERATIONS+1-1 downto 0)(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_dest_req_sizes_2d_arr         : slv_array_2d_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0)(log2(NUM_ITEMS)+1-1 downto 0);
    signal s_dest_req_pending_2d_arr       : slv_array_2d_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0)(NUM_ITERATIONS-1 downto 0);
    signal s_dest_req_sizes_updated_2d_arr : slv_array_2d_t(NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0)(log2(NUM_ITEMS)+1-1 downto 0);
    signal s_ip_port_conn_info_arr         : slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
    signal s_op_port_conn_info_arr         : slv_array_t   (NUM_PORTS-1 downto 0)(NUM_PORTS-1 downto 0);
begin

    s_dest_req_vec_2d_arr(0) <= slv_array_deser(DEST_REQ_VEC, NUM_PORTS);
    s_decision_reg_2d_arr(0) <= (others => (others => '0'));
    s_dest_req_sizes_2d_arr  <= slv_array_2d_deser(DEST_REQ_SIZES, NUM_PORTS, NUM_PORTS);

    islip_iterations_g : for k in 1 to NUM_ITERATIONS generate
        islip_iteration_i : entity work.ISLIP_ITERATION
        generic map (
            NUM_PORTS => NUM_PORTS,
            NUM_ITEMS => NUM_ITEMS,
            DEVICE    => DEVICE
        )
        port map (
            CLK               => CLK,
            RESET             => RESET,
            RX_DEST_REQ_VEC   => s_dest_req_vec_2d_arr(k-1),
            RX_DECISION_REG   => s_decision_reg_2d_arr(k-1),
            RX_DEST_REQ_SIZES => s_dest_req_sizes_updated_2d_arr,
            TX_DEST_REQ_VEC   => s_dest_req_vec_2d_arr(k),
            TX_DECISION_REG   => s_decision_reg_2d_arr(k)
        );
        dest_req_pending_ip_g : for i in 0 to NUM_PORTS-1 generate
            dest_req_pending_op_g : for j in 0 to NUM_PORTS-1 generate
                s_dest_req_pending_2d_arr(i)(j)(k-1) <= s_decision_reg_2d_arr(k)(i)(j);
            end generate;
        end generate;
    end generate;

    dest_req_sizes_updated_ip_g : for i in 0 to NUM_PORTS-1 generate
        dest_req_sizes_updated_op_g : for j in 0 to NUM_PORTS-1 generate
            signal s_num_requests_pending : std_logic_vector(log2(NUM_ITEMS)+1-1 downto 0);
            signal s_difference           : unsigned(log2(NUM_ITEMS)+1-1 downto 0);
            signal s_difference_vld       : std_logic;
        begin
            s_num_requests_pending                <= std_logic_vector(to_unsigned(count_ones(s_dest_req_pending_2d_arr(i)(j)), log2(NUM_ITEMS)+1));
            s_difference                          <= unsigned(s_dest_req_sizes_2d_arr(i)(j)) - unsigned(s_num_requests_pending);
            s_difference_vld                      <= '1' when s_dest_req_sizes_2d_arr(i)(j) > s_num_requests_pending else '0';
            s_dest_req_sizes_updated_2d_arr(i)(j) <= std_logic_vector(s_difference) when s_difference_vld = '1' else (others => '0');
        end generate;
    end generate;

    port_conn_info_rows_g : for i in 0 to NUM_PORTS-1 generate
        port_conn_info_cols_g : for j in 0 to NUM_PORTS-1 generate
            s_ip_port_conn_info_arr(i)(j) <= s_decision_reg_2d_arr(NUM_ITERATIONS)(i)(j);
            s_op_port_conn_info_arr(i)(j) <= s_decision_reg_2d_arr(NUM_ITERATIONS)(j)(i);
        end generate;
    end generate;

    port_conn_signals_g : for i in 0 to NUM_PORTS-1 generate
        IP_CONN_VLD(i) <= or s_ip_port_conn_info_arr(i);
        OP_CONN_VLD(i) <= or s_op_port_conn_info_arr(i);

        ip_conn_sel_enc_i : entity work.GEN_ENC
        generic map (
            ITEMS  => NUM_PORTS,
            DEVICE => DEVICE
        )
        port map (
            DI   => s_ip_port_conn_info_arr(i),
            ADDR => IP_CONN_SEL((i+1)*log2(NUM_PORTS)-1 downto i*log2(NUM_PORTS))
        );

        op_conn_sel_enc_i : entity work.GEN_ENC
        generic map (
            ITEMS  => NUM_PORTS,
            DEVICE => DEVICE
        )
        port map (
            DI   => s_op_port_conn_info_arr(i),
            ADDR => OP_CONN_SEL((i+1)*log2(NUM_PORTS)-1 downto i*log2(NUM_PORTS))
        );
    end generate;

end architecture;
