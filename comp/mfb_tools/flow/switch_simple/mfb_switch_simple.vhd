-- mfb_switch_simple.vhd:
-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity MFB_SWITCH_SIMPLE is
    generic (
        PORTS       : natural := 2;
        REGIONS     : natural := 4;
        REGION_SIZE : natural := 8;
        BLOCK_SIZE  : natural := 8;
        ITEM_WIDTH  : natural := 8;
        META_WIDTH  : natural := 1;
        FIFO_DEPTH  : natural := 512;
        -- Enable masking SOF and EOF due to switch to the other input.
        MASKING_EN  : boolean := True;
        -- Maximum amount of clock periods with destination ready before
        -- it tries to switch to the other input.
        CNT_MAX     : integer := 64;
        -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE      : string := "AGILEX"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- Multiple input MFB interfaces
        -- =====================================================================
        RX_MFB_SEL     : in  slv_array_t(PORTS-1 downto 0)(REGIONS*max(1,log2(PORTS))-1 downto 0); -- valid with SOF
        RX_MFB_META    : in  slv_array_t(PORTS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_DATA    : in  slv_array_t(PORTS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  slv_array_t(PORTS-1 downto 0)(REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t(PORTS-1 downto 0)(REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t(PORTS-1 downto 0)(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t(PORTS-1 downto 0)(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(PORTS-1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(PORTS-1 downto 0);

        -- =====================================================================
        -- Multiple output MFB interfaces
        -- =====================================================================
        TX_MFB_META    : out slv_array_t(PORTS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
        TX_MFB_DATA    : out slv_array_t(PORTS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out slv_array_t(PORTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t(PORTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t(PORTS-1 downto 0)(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t(PORTS-1 downto 0)(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(PORTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(PORTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SWITCH_SIMPLE is

    constant SW_PATHS : natural := 2**PORTS;

    signal sw_mfb_meta_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
    signal sw_mfb_data_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal sw_mfb_sof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal sw_mfb_eof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal sw_mfb_sof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
    signal sw_mfb_eof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal sw_mfb_src_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);
    signal sw_mfb_dst_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);

    signal fo_mfb_meta_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
    signal fo_mfb_data_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal fo_mfb_sof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal fo_mfb_eof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal fo_mfb_sof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
    signal fo_mfb_eof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal fo_mfb_src_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);
    signal fo_mfb_dst_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);

    signal mx_mfb_meta_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0);
    signal mx_mfb_data_arr    : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
    signal mx_mfb_sof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal mx_mfb_eof_arr     : slv_array_t(SW_PATHS-1 downto 0)(REGIONS-1 downto 0);
    signal mx_mfb_sof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*max(1, log2(REGION_SIZE))-1 downto 0);
    signal mx_mfb_eof_pos_arr : slv_array_t(SW_PATHS-1 downto 0)(REGIONS*log2(REGION_SIZE*BLOCK_SIZE)-1 downto 0);
    signal mx_mfb_src_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);
    signal mx_mfb_dst_rdy_arr : std_logic_vector(SW_PATHS-1 downto 0);

begin

    en_g: if PORTS > 1 generate

        input_g : for ii in 0 to PORTS-1 generate
            split_i : entity work.MFB_SPLITTER_SIMPLE_GEN
            generic map (
                SPLITTER_OUTPUTS => PORTS,
                REGIONS          => REGIONS,
                REGION_SIZE      => REGION_SIZE,
                BLOCK_SIZE       => BLOCK_SIZE,
                ITEM_WIDTH       => ITEM_WIDTH,
                META_WIDTH       => META_WIDTH,
                DEVICE           => DEVICE
            )
            port map (
                CLK            => CLK,
                RESET          => RESET,

                RX_MFB_SEL     => RX_MFB_SEL(ii),
                RX_MFB_META    => RX_MFB_META(ii),
                RX_MFB_DATA    => RX_MFB_DATA(ii),
                RX_MFB_SOF     => RX_MFB_SOF(ii),
                RX_MFB_EOF     => RX_MFB_EOF(ii),
                RX_MFB_SOF_POS => RX_MFB_SOF_POS(ii),
                RX_MFB_EOF_POS => RX_MFB_EOF_POS(ii),
                RX_MFB_SRC_RDY => RX_MFB_SRC_RDY(ii),
                RX_MFB_DST_RDY => RX_MFB_DST_RDY(ii),

                TX_MFB_META    => sw_mfb_meta_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_DATA    => sw_mfb_data_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_SOF     => sw_mfb_sof_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_EOF     => sw_mfb_eof_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_SOF_POS => sw_mfb_sof_pos_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_EOF_POS => sw_mfb_eof_pos_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_SRC_RDY => sw_mfb_src_rdy_arr((ii+1)*PORTS-1 downto ii*PORTS),
                TX_MFB_DST_RDY => sw_mfb_dst_rdy_arr((ii+1)*PORTS-1 downto ii*PORTS)
            );
        end generate;

        fifo_g : for ii in 0 to SW_PATHS-1 generate
            fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS     => REGIONS,
                REGION_SIZE => REGION_SIZE,
                BLOCK_SIZE  => BLOCK_SIZE,
                ITEM_WIDTH  => ITEM_WIDTH,
                META_WIDTH  => META_WIDTH,
                FIFO_DEPTH  => FIFO_DEPTH,
                RAM_TYPE    => "AUTO",
                DEVICE      => DEVICE
            )
            port map (
                CLK         => CLK,
                RST         => RESET,

                RX_DATA     => sw_mfb_data_arr(ii),
                RX_META     => sw_mfb_meta_arr(ii),
                RX_SOF_POS  => sw_mfb_sof_pos_arr(ii),
                RX_EOF_POS  => sw_mfb_eof_pos_arr(ii),
                RX_SOF      => sw_mfb_sof_arr(ii),
                RX_EOF      => sw_mfb_eof_arr(ii),
                RX_SRC_RDY  => sw_mfb_src_rdy_arr(ii),
                RX_DST_RDY  => sw_mfb_dst_rdy_arr(ii),

                TX_DATA     => fo_mfb_data_arr(ii),
                TX_META     => fo_mfb_meta_arr(ii),
                TX_SOF_POS  => fo_mfb_sof_pos_arr(ii),
                TX_EOF_POS  => fo_mfb_eof_pos_arr(ii),
                TX_SOF      => fo_mfb_sof_arr(ii),
                TX_EOF      => fo_mfb_eof_arr(ii),
                TX_SRC_RDY  => fo_mfb_src_rdy_arr(ii),
                TX_DST_RDY  => fo_mfb_dst_rdy_arr(ii)
            );
        end generate;

        matrix_g : for ii in 0 to PORTS-1 generate
            matrix_g2 : for jj in 0 to PORTS-1 generate
                mx_mfb_data_arr(ii*PORTS+jj)    <= fo_mfb_data_arr(jj*PORTS+ii);
                mx_mfb_meta_arr(ii*PORTS+jj)    <= fo_mfb_meta_arr(jj*PORTS+ii);
                mx_mfb_sof_pos_arr(ii*PORTS+jj) <= fo_mfb_sof_pos_arr(jj*PORTS+ii);
                mx_mfb_eof_pos_arr(ii*PORTS+jj) <= fo_mfb_eof_pos_arr(jj*PORTS+ii);
                mx_mfb_sof_arr(ii*PORTS+jj)     <= fo_mfb_sof_arr(jj*PORTS+ii);
                mx_mfb_eof_arr(ii*PORTS+jj)     <= fo_mfb_eof_arr(jj*PORTS+ii);
                mx_mfb_src_rdy_arr(ii*PORTS+jj) <= fo_mfb_src_rdy_arr(jj*PORTS+ii);
                fo_mfb_dst_rdy_arr(jj*PORTS+ii) <= mx_mfb_dst_rdy_arr(ii*PORTS+jj);
            end generate;
        end generate;

        output_g : for ii in 0 to PORTS-1 generate
            merge_i : entity work.MFB_MERGER_SIMPLE_GEN
            generic map (
                MERGER_INPUTS   => PORTS,
                MFB_REGIONS     => REGIONS,
                MFB_REGION_SIZE => REGION_SIZE,
                MFB_BLOCK_SIZE  => BLOCK_SIZE,
                MFB_ITEM_WIDTH  => ITEM_WIDTH,
                MFB_META_WIDTH  => META_WIDTH,
                MASKING_EN      => MASKING_EN,
                CNT_MAX         => CNT_MAX
            )
            port map (
                CLK            => CLK,
                RST            => RESET,

                RX_MFB_META    => mx_mfb_meta_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_DATA    => mx_mfb_data_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_SOF     => mx_mfb_sof_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_EOF     => mx_mfb_eof_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_SOF_POS => mx_mfb_sof_pos_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_EOF_POS => mx_mfb_eof_pos_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_SRC_RDY => mx_mfb_src_rdy_arr((ii+1)*PORTS-1 downto ii*PORTS),
                RX_MFB_DST_RDY => mx_mfb_dst_rdy_arr((ii+1)*PORTS-1 downto ii*PORTS),

                TX_MFB_META    => TX_MFB_META(ii),
                TX_MFB_DATA    => TX_MFB_DATA(ii),
                TX_MFB_SOF     => TX_MFB_SOF(ii),
                TX_MFB_EOF     => TX_MFB_EOF(ii),
                TX_MFB_SOF_POS => TX_MFB_SOF_POS(ii),
                TX_MFB_EOF_POS => TX_MFB_EOF_POS(ii),
                TX_MFB_SRC_RDY => TX_MFB_SRC_RDY(ii),
                TX_MFB_DST_RDY => TX_MFB_DST_RDY(ii)
            );
        end generate;

    else generate

        TX_MFB_META    <= RX_MFB_META;
        TX_MFB_DATA    <= RX_MFB_DATA;
        TX_MFB_SOF     <= RX_MFB_SOF;
        TX_MFB_EOF     <= RX_MFB_EOF;
        TX_MFB_SOF_POS <= RX_MFB_SOF_POS;
        TX_MFB_EOF_POS <= RX_MFB_EOF_POS;
        TX_MFB_SRC_RDY <= RX_MFB_SRC_RDY;
        RX_MFB_DST_RDY <= TX_MFB_DST_RDY;

    end generate;

end architecture;
