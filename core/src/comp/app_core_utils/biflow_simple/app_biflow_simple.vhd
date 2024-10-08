-- app_biflow_simple.vhd:
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity APP_BIFLOW_SIMPLE is
generic (
    IN_STREAMS            : natural := 1;
    OUT_STREAMS           : natural := 2;
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
    CLK              : in  std_logic;
    RESET            : in  std_logic;
    
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

architecture FULL of APP_BIFLOW_SIMPLE is

    constant IN_PER_OUT : natural := IN_STREAMS/OUT_STREAMS;
    constant SW_PORTS   : natural := IN_STREAMS*OUT_STREAMS;

    signal port_in_mvb_data       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal port_in_mvb_sel        : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(OUT_STREAMS))-1 downto 0);
    signal port_in_mvb_vld        : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_in_mvb_src_rdy    : std_logic_vector(SW_PORTS-1 downto 0);
    signal port_in_mvb_dst_rdy    : std_logic_vector(SW_PORTS-1 downto 0);

    signal port_in_mfb_data       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal port_in_mfb_sof        : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_in_mfb_eof        : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_in_mfb_sof_pos    : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal port_in_mfb_eof_pos    : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal port_in_mfb_src_rdy    : std_logic_vector(SW_PORTS-1 downto 0);
    signal port_in_mfb_dst_rdy    : std_logic_vector(SW_PORTS-1 downto 0);

    signal port_out_mvb_data      : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal port_out_mvb_sel       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(OUT_STREAMS))-1 downto 0);
    signal port_out_mvb_vld       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_out_mvb_src_rdy   : std_logic_vector(SW_PORTS-1 downto 0);
    signal port_out_mvb_dst_rdy   : std_logic_vector(SW_PORTS-1 downto 0);

    signal port_out_mfb_data      : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal port_out_mfb_sof       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_out_mfb_eof       : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal port_out_mfb_sof_pos   : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal port_out_mfb_eof_pos   : slv_array_t(SW_PORTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal port_out_mfb_src_rdy   : std_logic_vector(SW_PORTS-1 downto 0);
    signal port_out_mfb_dst_rdy   : std_logic_vector(SW_PORTS-1 downto 0);

begin

    --assert ((OUT_STREAMS = IN_STREAMS) or (OUT_STREAMS < IN_STREAMS and OUT_STREAMS = 1))
    --    report "APP_BIFLOW_SIMPLE: The number of OUT_STREAMS must be equal to IN_STREAMS, or OUT_STREAMS must be 1 and OUT_STREAMS < IN_STREAMS!"
    --    severity failure;

    -- simple connection
    no_biflow_g: if (OUT_STREAMS = 1 and IN_STREAMS = 1) generate
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

    -- Biflow merger
    biflow_g: if ((IN_STREAMS > 1 or OUT_STREAMS > 1)) generate
        biflow_port_g: for i in 0 to IN_STREAMS-1 generate
            subtype IPO_RANGE is natural range (i+1)*(OUT_STREAMS)-1 downto i*(OUT_STREAMS);
        begin
            biflow_port_i : entity work.APP_BIFLOW_PORT
            generic map(
                IN_STREAMS      => 1,
                OUT_STREAMS     => OUT_STREAMS,
                MFB_REGIONS     => MFB_REGIONS,
                MFB_REGION_SIZE => MFB_REGION_SIZE,
                MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
                MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
                MVB_ITEM_WIDTH  => MVB_ITEM_WIDTH,
                DEVICE          => DEVICE
            )
            port map(
                CLK             => CLK,
                RESET           => RESET,

                IN_MVB_DATA(0)     => IN_MVB_DATA(i),
                IN_MVB_SEL(0)      => IN_MVB_SEL(i),
                IN_MVB_VLD(0)      => IN_MVB_VLD(i),
                IN_MVB_SRC_RDY(0)  => IN_MVB_SRC_RDY(i),
                IN_MVB_DST_RDY(0)  => IN_MVB_DST_RDY(i),

                IN_MFB_DATA(0)     => IN_MFB_DATA(i),
                IN_MFB_SOF(0)      => IN_MFB_SOF(i),
                IN_MFB_EOF(0)      => IN_MFB_EOF(i),
                IN_MFB_SOF_POS(0)  => IN_MFB_SOF_POS(i),
                IN_MFB_EOF_POS(0)  => IN_MFB_EOF_POS(i),
                IN_MFB_SRC_RDY(0)  => IN_MFB_SRC_RDY(i),
                IN_MFB_DST_RDY(0)  => IN_MFB_DST_RDY(i),

                OUT_MVB_DATA    => port_in_mvb_data(IPO_RANGE),
                OUT_MVB_VLD     => port_in_mvb_vld(IPO_RANGE),
                OUT_MVB_SRC_RDY => port_in_mvb_src_rdy(IPO_RANGE),
                OUT_MVB_DST_RDY => port_in_mvb_dst_rdy(IPO_RANGE),

                OUT_MFB_DATA    => port_in_mfb_data(IPO_RANGE),
                OUT_MFB_SOF     => port_in_mfb_sof(IPO_RANGE),
                OUT_MFB_EOF     => port_in_mfb_eof(IPO_RANGE),
                OUT_MFB_SOF_POS => port_in_mfb_sof_pos(IPO_RANGE),
                OUT_MFB_EOF_POS => port_in_mfb_eof_pos(IPO_RANGE),
                OUT_MFB_SRC_RDY => port_in_mfb_src_rdy(IPO_RANGE),
                OUT_MFB_DST_RDY => port_in_mfb_dst_rdy(IPO_RANGE)
            );
        end generate;

        out_merge_g: for i in 0 to OUT_STREAMS-1 generate
            subtype IPO_RANGE is natural range (i+1)*(IN_STREAMS)-1 downto i*(IN_STREAMS);
        begin

            -- remap ports
            port_out_g: for j in 0 to IN_STREAMS-1 generate
                port_out_mvb_data(i*IN_STREAMS+j)    <= port_in_mvb_data(j*OUT_STREAMS+i);
                port_out_mvb_vld(i*IN_STREAMS+j)     <= port_in_mvb_vld(j*OUT_STREAMS+i);
                port_out_mvb_src_rdy(i*IN_STREAMS+j) <= port_in_mvb_src_rdy(j*OUT_STREAMS+i);
                port_in_mvb_dst_rdy(j*OUT_STREAMS+i)  <= port_out_mvb_dst_rdy(i*IN_STREAMS+j);
                
                port_out_mfb_data(i*IN_STREAMS+j)    <= port_in_mfb_data(j*OUT_STREAMS+i);
                port_out_mfb_sof(i*IN_STREAMS+j)     <= port_in_mfb_sof(j*OUT_STREAMS+i);
                port_out_mfb_eof(i*IN_STREAMS+j)     <= port_in_mfb_eof(j*OUT_STREAMS+i);
                port_out_mfb_sof_pos(i*IN_STREAMS+j) <= port_in_mfb_sof_pos(j*OUT_STREAMS+i);
                port_out_mfb_eof_pos(i*IN_STREAMS+j) <= port_in_mfb_eof_pos(j*OUT_STREAMS+i);
                port_out_mfb_src_rdy(i*IN_STREAMS+j) <= port_in_mfb_src_rdy(j*OUT_STREAMS+i);
                port_in_mfb_dst_rdy(j*OUT_STREAMS+i)  <= port_out_mfb_dst_rdy(i*IN_STREAMS+j);
            end generate;

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
                OUT_PIPE_EN     => true,
                DEVICE          => DEVICE
            )
            port map(
                CLK             => CLK,
                RESET           => RESET,
                    
                RX_MVB_DATA     => port_out_mvb_data(IPO_RANGE),
                RX_MVB_PAYLOAD  => (others => (others => '1')),
                RX_MVB_VLD      => port_out_mvb_vld(IPO_RANGE),
                RX_MVB_SRC_RDY  => port_out_mvb_src_rdy(IPO_RANGE),
                RX_MVB_DST_RDY  => port_out_mvb_dst_rdy(IPO_RANGE),

                RX_MFB_DATA     => port_out_mfb_data(IPO_RANGE),
                RX_MFB_SOF      => port_out_mfb_sof(IPO_RANGE),
                RX_MFB_EOF      => port_out_mfb_eof(IPO_RANGE),
                RX_MFB_SOF_POS  => port_out_mfb_sof_pos(IPO_RANGE),
                RX_MFB_EOF_POS  => port_out_mfb_eof_pos(IPO_RANGE),
                RX_MFB_SRC_RDY  => port_out_mfb_src_rdy(IPO_RANGE),
                RX_MFB_DST_RDY  => port_out_mfb_dst_rdy(IPO_RANGE),

                TX_MVB_DATA     => OUT_MVB_DATA(i),
                TX_MVB_VLD      => OUT_MVB_VLD(i),
                TX_MVB_SRC_RDY  => OUT_MVB_SRC_RDY(i),
                TX_MVB_DST_RDY  => OUT_MVB_DST_RDY(i),

                TX_MFB_DATA     => OUT_MFB_DATA(i),
                TX_MFB_SOF      => OUT_MFB_SOF(i),
                TX_MFB_EOF      => OUT_MFB_EOF(i),
                TX_MFB_SOF_POS  => OUT_MFB_SOF_POS(i),
                TX_MFB_EOF_POS  => OUT_MFB_EOF_POS(i),
                TX_MFB_SRC_RDY  => OUT_MFB_SRC_RDY(i),
                TX_MFB_DST_RDY  => OUT_MFB_DST_RDY(i)
            );
        end generate;
    end generate;
end architecture;
