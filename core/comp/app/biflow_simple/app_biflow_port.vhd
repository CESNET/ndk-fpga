-- app_biflow_port.vhd
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity APP_BIFLOW_PORT is
generic (
    IN_STREAMS            : natural := 2;
    OUT_STREAMS           : natural := 1;
    MFB_REGIONS           : natural := 1;
    MFB_REGION_SIZE       : natural := 8;
    MFB_BLOCK_SIZE        : natural := 8;
    MFB_ITEM_WIDTH        : natural := 8;
    MVB_ITEM_WIDTH        : natural := 8;
    MVB_FIFO_DEPTH        : natural := 32;
    MFB_FIFO_DEPTH        : natural := 512;
    MFB_FIFO_ENABLE       : boolean := True;
    MFB_FIFO_TYPE         : string  := "AUTO";
    DEVICE                : string  := "AGILEX"
);
port (
    -- =========================================================================
    -- Clock and Resets inputs
    -- =========================================================================
    CLK             : in  std_logic;
    RESET           : in  std_logic;
    
    -- =========================================================================
    -- Input MFB+MVB interface
    -- =========================================================================
    IN_MVB_DATA      : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    IN_MVB_SEL       : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(OUT_STREAMS))-1 downto 0);
    IN_MVB_VLD       : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    IN_MVB_SRC_RDY   : in  std_logic_vector(IN_STREAMS-1 downto 0);
    IN_MVB_DST_RDY   : out std_logic_vector(IN_STREAMS-1 downto 0);

    IN_MFB_DATA      : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    IN_MFB_SOF       : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    IN_MFB_EOF       : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    IN_MFB_SOF_POS   : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    IN_MFB_EOF_POS   : in  slv_array_t(IN_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    IN_MFB_SRC_RDY   : in  std_logic_vector(IN_STREAMS-1 downto 0);
    IN_MFB_DST_RDY   : out std_logic_vector(IN_STREAMS-1 downto 0);
    
    -- =========================================================================
    -- Output MFB+MVB interface
    -- =========================================================================
    OUT_MVB_DATA     : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    OUT_MVB_VLD      : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    OUT_MVB_SRC_RDY  : out std_logic_vector(OUT_STREAMS-1 downto 0);
    OUT_MVB_DST_RDY  : in  std_logic_vector(OUT_STREAMS-1 downto 0);
    
    OUT_MFB_DATA     : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    OUT_MFB_SOF      : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    OUT_MFB_EOF      : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    OUT_MFB_SOF_POS  : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    OUT_MFB_EOF_POS  : out slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    OUT_MFB_SRC_RDY  : out std_logic_vector(OUT_STREAMS-1 downto 0);
    OUT_MFB_DST_RDY  : in  std_logic_vector(OUT_STREAMS-1 downto 0)
);
end entity;

architecture FULL of APP_BIFLOW_PORT is

    signal fi_mfb_data    : slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal fi_mfb_sof     : slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fi_mfb_eof     : slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal fi_mfb_sof_pos : slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal fi_mfb_eof_pos : slv_array_t(OUT_STREAMS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal fi_mfb_src_rdy : std_logic_vector(OUT_STREAMS-1 downto 0);
    signal fi_mfb_dst_rdy : std_logic_vector(OUT_STREAMS-1 downto 0);

begin

    fake_g: if (IN_STREAMS = OUT_STREAMS) generate
        OUT_MVB_DATA    <= IN_MVB_DATA;
        OUT_MVB_VLD     <= IN_MVB_VLD;
        OUT_MVB_SRC_RDY <= IN_MVB_SRC_RDY;
        IN_MVB_DST_RDY  <= OUT_MVB_DST_RDY;

        OUT_MFB_DATA    <= IN_MFB_DATA;
        OUT_MFB_SOF     <= IN_MFB_SOF;
        OUT_MFB_EOF     <= IN_MFB_EOF;
        OUT_MFB_SOF_POS <= IN_MFB_SOF_POS;
        OUT_MFB_EOF_POS <= IN_MFB_EOF_POS;
        OUT_MFB_SRC_RDY <= IN_MFB_SRC_RDY;
        IN_MFB_DST_RDY  <= OUT_MFB_DST_RDY;
    end generate;

    merger_g: if (IN_STREAMS > 1 and OUT_STREAMS = 1) generate
        mfb_merger_tree_i : entity work.MFB_MERGER_GEN
        generic map(
            MERGER_INPUTS   => IN_STREAMS,
            MVB_ITEMS       => MFB_REGIONS,
            MVB_ITEM_WIDTH  => MVB_ITEM_WIDTH,
            MFB_REGIONS     => MFB_REGIONS,
            MFB_REG_SIZE    => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
            INPUT_FIFO_SIZE => 32,
            RX_PAYLOAD_EN   => (others => true),
            IN_PIPE_EN      => false,
            OUT_PIPE_EN     => false,
            DEVICE          => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,
                
            RX_MVB_DATA     => IN_MVB_DATA,
            RX_MVB_PAYLOAD  => (others => (others => '1')),
            RX_MVB_VLD      => IN_MVB_VLD,
            RX_MVB_SRC_RDY  => IN_MVB_SRC_RDY,
            RX_MVB_DST_RDY  => IN_MVB_DST_RDY,

            RX_MFB_DATA     => IN_MFB_DATA,
            RX_MFB_SOF      => IN_MFB_SOF,
            RX_MFB_EOF      => IN_MFB_EOF,
            RX_MFB_SOF_POS  => IN_MFB_SOF_POS,
            RX_MFB_EOF_POS  => IN_MFB_EOF_POS,
            RX_MFB_SRC_RDY  => IN_MFB_SRC_RDY,
            RX_MFB_DST_RDY  => IN_MFB_DST_RDY,

            TX_MVB_DATA     => OUT_MVB_DATA(0),
            TX_MVB_VLD      => OUT_MVB_VLD(0),
            TX_MVB_SRC_RDY  => OUT_MVB_SRC_RDY(0),
            TX_MVB_DST_RDY  => OUT_MVB_DST_RDY(0),

            TX_MFB_DATA     => fi_mfb_data(0),
            TX_MFB_SOF      => fi_mfb_sof(0),
            TX_MFB_EOF      => fi_mfb_eof(0),
            TX_MFB_SOF_POS  => fi_mfb_sof_pos(0),
            TX_MFB_EOF_POS  => fi_mfb_eof_pos(0),
            TX_MFB_SRC_RDY  => fi_mfb_src_rdy(0),
            TX_MFB_DST_RDY  => fi_mfb_dst_rdy(0)
        );

        fifo_g: if MFB_FIFO_ENABLE generate
            mfb_fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REGION_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                FIFO_DEPTH  => MFB_FIFO_DEPTH,
                RAM_TYPE    => MFB_FIFO_TYPE,
                DEVICE      => DEVICE
            )
            port map (
                CLK         => CLK,
                RST         => RESET,
            
                RX_DATA     => fi_mfb_data(0),
                RX_SOF_POS  => fi_mfb_sof_pos(0),
                RX_EOF_POS  => fi_mfb_eof_pos(0),
                RX_SOF      => fi_mfb_sof(0),
                RX_EOF      => fi_mfb_eof(0),
                RX_SRC_RDY  => fi_mfb_src_rdy(0),
                RX_DST_RDY  => fi_mfb_dst_rdy(0),
            
                TX_DATA     => OUT_MFB_DATA(0),
                TX_SOF_POS  => OUT_MFB_SOF_POS(0),
                TX_EOF_POS  => OUT_MFB_EOF_POS(0),
                TX_SOF      => OUT_MFB_SOF(0),
                TX_EOF      => OUT_MFB_EOF(0),
                TX_SRC_RDY  => OUT_MFB_SRC_RDY(0),
                TX_DST_RDY  => OUT_MFB_DST_RDY(0)
            );
        else generate
            OUT_MFB_DATA(0)    <= fi_mfb_data(0);
            OUT_MFB_SOF_POS(0) <= fi_mfb_sof_pos(0);
            OUT_MFB_EOF_POS(0) <= fi_mfb_eof_pos(0);
            OUT_MFB_SOF(0)     <= fi_mfb_sof(0);
            OUT_MFB_EOF(0)     <= fi_mfb_eof(0);
            OUT_MFB_SRC_RDY(0) <= fi_mfb_src_rdy(0);
            fi_mfb_dst_rdy(0)  <= OUT_MFB_DST_RDY(0);
        end generate;
    end generate;

    splitter_g: if (IN_STREAMS = 1 and OUT_STREAMS > 1) generate
        mfb_splitter_tree_i : entity work.MFB_SPLITTER_GEN
        generic map(
            SPLITTER_OUTPUTS => OUT_STREAMS,
            MVB_ITEMS        => MFB_REGIONS,
            MVB_ITEM_WIDTH   => MVB_ITEM_WIDTH,
            MFB_REGIONS      => MFB_REGIONS,
            MFB_REG_SIZE     => MFB_REGION_SIZE,
            MFB_BLOCK_SIZE   => MFB_BLOCK_SIZE,
            MFB_ITEM_WIDTH   => MFB_ITEM_WIDTH,
            OUTPUT_FIFO_SIZE => MVB_FIFO_DEPTH,
            OUT_PIPE_EN      => false,
            DEVICE           => DEVICE
        )
        port map(
            CLK             => CLK,
            RESET           => RESET,

            RX_MVB_DATA     => IN_MVB_DATA(0),
            RX_MVB_SWITCH   => IN_MVB_SEL(0),
            RX_MVB_PAYLOAD  => (others => '1'),
            RX_MVB_VLD      => IN_MVB_VLD(0),
            RX_MVB_SRC_RDY  => IN_MVB_SRC_RDY(0),
            RX_MVB_DST_RDY  => IN_MVB_DST_RDY(0),

            RX_MFB_DATA     => IN_MFB_DATA(0),
            RX_MFB_SOF      => IN_MFB_SOF(0),
            RX_MFB_EOF      => IN_MFB_EOF(0),
            RX_MFB_SOF_POS  => IN_MFB_SOF_POS(0),
            RX_MFB_EOF_POS  => IN_MFB_EOF_POS(0),
            RX_MFB_SRC_RDY  => IN_MFB_SRC_RDY(0),
            RX_MFB_DST_RDY  => IN_MFB_DST_RDY(0),

            TX_MVB_DATA     => OUT_MVB_DATA,
            TX_MVB_VLD      => OUT_MVB_VLD,
            TX_MVB_SRC_RDY  => OUT_MVB_SRC_RDY,
            TX_MVB_DST_RDY  => OUT_MVB_DST_RDY,

            TX_MFB_DATA     => fi_mfb_data,
            TX_MFB_SOF      => fi_mfb_sof,
            TX_MFB_EOF      => fi_mfb_eof,
            TX_MFB_SOF_POS  => fi_mfb_sof_pos,
            TX_MFB_EOF_POS  => fi_mfb_eof_pos,
            TX_MFB_SRC_RDY  => fi_mfb_src_rdy,
            TX_MFB_DST_RDY  => fi_mfb_dst_rdy
        );

        fifo_g: if MFB_FIFO_ENABLE generate
            mfb_fifo_g: for i in 0 to OUT_STREAMS-1 generate
                mfb_fifo_i : entity work.MFB_FIFOX
                generic map (
                    REGIONS     => MFB_REGIONS,
                    REGION_SIZE => MFB_REGION_SIZE,
                    BLOCK_SIZE  => MFB_BLOCK_SIZE,
                    ITEM_WIDTH  => MFB_ITEM_WIDTH,
                    FIFO_DEPTH  => MFB_FIFO_DEPTH,
                    RAM_TYPE    => MFB_FIFO_TYPE,
                    DEVICE      => DEVICE
                )
                port map (
                    CLK         => CLK,
                    RST         => RESET,
                
                    RX_DATA     => fi_mfb_data(i),
                    RX_SOF_POS  => fi_mfb_sof_pos(i),
                    RX_EOF_POS  => fi_mfb_eof_pos(i),
                    RX_SOF      => fi_mfb_sof(i),
                    RX_EOF      => fi_mfb_eof(i),
                    RX_SRC_RDY  => fi_mfb_src_rdy(i),
                    RX_DST_RDY  => fi_mfb_dst_rdy(i),
                
                    TX_DATA     => OUT_MFB_DATA(i),
                    TX_SOF_POS  => OUT_MFB_SOF_POS(i),
                    TX_EOF_POS  => OUT_MFB_EOF_POS(i),
                    TX_SOF      => OUT_MFB_SOF(i),
                    TX_EOF      => OUT_MFB_EOF(i),
                    TX_SRC_RDY  => OUT_MFB_SRC_RDY(i),
                    TX_DST_RDY  => OUT_MFB_DST_RDY(i)
                );
            end generate;
        else generate
            OUT_MFB_DATA    <= fi_mfb_data;
            OUT_MFB_SOF_POS <= fi_mfb_sof_pos;
            OUT_MFB_EOF_POS <= fi_mfb_eof_pos;
            OUT_MFB_SOF     <= fi_mfb_sof;
            OUT_MFB_EOF     <= fi_mfb_eof;
            OUT_MFB_SRC_RDY <= fi_mfb_src_rdy;
            fi_mfb_dst_rdy  <= OUT_MFB_DST_RDY;
        end generate;
    end generate;

end architecture;
