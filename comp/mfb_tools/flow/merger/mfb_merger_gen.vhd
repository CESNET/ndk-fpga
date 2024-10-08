-- mfb_merger_gen.vhd: MFB+MVB bus merger with generic number of inputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

-- MFB+MVB bus merger with generic number of inputs
entity MFB_MERGER_GEN is
    generic(
        -- number of merger inputs
        MERGER_INPUTS   : integer := 2;

        -- =============================
        -- MVB characteristics
        -- =============================

        -- number of headers
        MVB_ITEMS       : integer := 2;
        -- width of header
        MVB_ITEM_WIDTH  : integer := 32;

        -- =============================
        -- MFB characteristics
        -- =============================

        -- number of regions in word
        MFB_REGIONS     : integer := 2;
        -- number of blocks in region
        MFB_REG_SIZE    : integer := 1;
        -- number of items in block
        MFB_BLOCK_SIZE  : integer := 8;
        -- width  of one item (in bits)
        MFB_ITEM_WIDTH  : integer := 32;
        -- width of MFB metadata
        MFB_META_WIDTH  : integer := 1;

        -- =============================
        -- Others
        -- =============================

        -- Size of input MVB and MFB FIFOs (in words)
        -- Minimum value is 2!
        INPUT_FIFO_SIZE : integer := 8;

        -- Data/Payload MFB interface required/active on individual input ports
        -- Currently used only in SIMPLE architecture to optimize usage of input/output pipes
        RX_PAYLOAD_EN   : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);

        -- Width of timeout counter, determines the time when the switch to
        -- the next active MVB/MFB stream occurs.
        SW_TIMEOUT_WIDTH : natural := 4;

        -- Input PIPEs enable for all 2:1 Mergers
        -- Input registers is created when this is set to false.
        IN_PIPE_EN      : boolean := false;

        -- Output PIPE enable for all 2:1 Mergers
        -- Output register is created when this is set to false.
        OUT_PIPE_EN     : boolean := true;

        -- "ULTRASCALE", "STRATIX10",...
        DEVICE          : string  := "ULTRASCALE"
    );
    port(
        -- =============================
        -- Common interface
        -- =============================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =============================
        -- RX interfaces
        -- =============================

        RX_MVB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- the header is associated with a payload frame on MFB
        RX_MVB_PAYLOAD : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MVB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        RX_MFB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Allways valid, metadata merged by words
        RX_MFB_META    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MFB_SOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        -- =============================
        -- TX interface
        -- =============================

        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- the header is associated with a payload frame on MFB
        TX_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- Allways valid, metadata merged by words
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_MERGER_GEN is

    constant TREE_STAGES         : natural := log2(MERGER_INPUTS);
    constant MERGER_INPUTS_2_POW : natural := 2**TREE_STAGES;

    function rx_payload_en_2_pow_init return b_array_t is
        variable tmp : b_array_t(MERGER_INPUTS_2_POW-1 downto 0) := (others => false);
    begin
        tmp(MERGER_INPUTS-1 downto 0) := RX_PAYLOAD_EN;
        return tmp;
    end function;

    constant RX_PAYLOAD_EN_2_POW : b_array_t(MERGER_INPUTS_2_POW-1 downto 0) := rx_payload_en_2_pow_init;

    function get_payload_en (stage, index : integer) return boolean;

    function get_payload_en (stage, index : integer) return boolean is
    begin
        --JC: Reports do not work in Vivado!
        --report "inputs " & to_string(MERGER_INPUTS) & "; inputs 2 pow " & to_string(MERGER_INPUTS_2_POW) & "; stages " & to_string(TREE_STAGES);
        --report "gen_payload_en ( " & to_string(stage) & " , " & to_string(index) & " )";
        if (stage /= 0) then
            -- Recursive call to previous stage
            return get_payload_en(stage-1,2*index) or get_payload_en(stage-1,2*index+1);
        else
            -- End of recursion -> user input
            return RX_PAYLOAD_EN_2_POW(index);
        end if;
    end function;

    signal s_rx_mvb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mvb_payload : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_vld     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MVB_ITEMS-1 downto 0) := (others => (others => (others => '0')));
    signal s_rx_mvb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0) := (others => (others => '0'));
    signal s_rx_mvb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);
    signal s_rx_mfb_data    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal s_rx_mfb_meta    : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    signal s_rx_mfb_sof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_eof     : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal s_rx_mfb_sof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal s_rx_mfb_eof_pos : slv_array_2d_t(TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal s_rx_mfb_src_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);
    signal s_rx_mfb_dst_rdy : slv_array_t   (TREE_STAGES+1-1 downto 0)(MERGER_INPUTS_2_POW-1 downto 0);

begin

    inputs_g : for i in 0 to MERGER_INPUTS-1 generate

        s_rx_mvb_data   (0)(i) <= RX_MVB_DATA   (i);
        s_rx_mvb_payload(0)(i) <= RX_MVB_PAYLOAD(i);
        s_rx_mvb_vld    (0)(i) <= RX_MVB_VLD    (i);
        s_rx_mvb_src_rdy(0)(i) <= RX_MVB_SRC_RDY(i);

        RX_MVB_DST_RDY(i)      <= s_rx_mvb_dst_rdy(0)(i);

        s_rx_mfb_data   (0)(i) <= RX_MFB_DATA   (i);
        s_rx_mfb_meta   (0)(i) <= RX_MFB_META   (i);
        s_rx_mfb_sof    (0)(i) <= RX_MFB_SOF    (i);
        s_rx_mfb_eof    (0)(i) <= RX_MFB_EOF    (i);
        s_rx_mfb_sof_pos(0)(i) <= RX_MFB_SOF_POS(i);
        s_rx_mfb_eof_pos(0)(i) <= RX_MFB_EOF_POS(i);
        s_rx_mfb_src_rdy(0)(i) <= RX_MFB_SRC_RDY(i);

        RX_MFB_DST_RDY(i)      <= s_rx_mfb_dst_rdy(0)(i);

    end generate;

    stage_g : for s in 0 to TREE_STAGES-1 generate
        merger_g : for i in 0 to (2**(TREE_STAGES-s-1))-1 generate
            merger_i: entity work.MFB_MERGER(FULL)
            generic map (
                MVB_ITEMS           => MVB_ITEMS              ,
                MFB_REGIONS         => MFB_REGIONS            ,
                MFB_REG_SIZE        => MFB_REG_SIZE           ,
                MFB_BLOCK_SIZE      => MFB_BLOCK_SIZE         ,
                MFB_ITEM_WIDTH      => MFB_ITEM_WIDTH         ,
                MFB_META_WIDTH      => MFB_META_WIDTH         ,
                HDR_WIDTH           => MVB_ITEM_WIDTH         ,
                RX0_PAYLOAD_ENABLED => get_payload_en(s,2*i  ),
                RX1_PAYLOAD_ENABLED => get_payload_en(s,2*i+1),
                INPUT_FIFO_SIZE     => INPUT_FIFO_SIZE        ,
                SW_TIMEOUT_WIDTH    => SW_TIMEOUT_WIDTH       ,
                IN_PIPE_EN          => IN_PIPE_EN             ,
                OUT_PIPE_EN         => OUT_PIPE_EN            ,
                DEVICE              => DEVICE
            )
            port map (
                CLK             => CLK  ,
                RESET           => RESET,

                RX0_MVB_HDR     => s_rx_mvb_data   (s)(2*i),
                RX0_MVB_PAYLOAD => s_rx_mvb_payload(s)(2*i),
                RX0_MVB_VLD     => s_rx_mvb_vld    (s)(2*i),
                RX0_MVB_SRC_RDY => s_rx_mvb_src_rdy(s)(2*i),
                RX0_MVB_DST_RDY => s_rx_mvb_dst_rdy(s)(2*i),
                RX0_MFB_DATA    => s_rx_mfb_data   (s)(2*i),
                RX0_MFB_META    => s_rx_mfb_meta   (s)(2*i),
                RX0_MFB_SOF     => s_rx_mfb_sof    (s)(2*i),
                RX0_MFB_EOF     => s_rx_mfb_eof    (s)(2*i),
                RX0_MFB_SOF_POS => s_rx_mfb_sof_pos(s)(2*i),
                RX0_MFB_EOF_POS => s_rx_mfb_eof_pos(s)(2*i),
                RX0_MFB_SRC_RDY => s_rx_mfb_src_rdy(s)(2*i),
                RX0_MFB_DST_RDY => s_rx_mfb_dst_rdy(s)(2*i),

                RX1_MVB_HDR     => s_rx_mvb_data   (s)(2*i+1),
                RX1_MVB_PAYLOAD => s_rx_mvb_payload(s)(2*i+1),
                RX1_MVB_VLD     => s_rx_mvb_vld    (s)(2*i+1),
                RX1_MVB_SRC_RDY => s_rx_mvb_src_rdy(s)(2*i+1),
                RX1_MVB_DST_RDY => s_rx_mvb_dst_rdy(s)(2*i+1),
                RX1_MFB_DATA    => s_rx_mfb_data   (s)(2*i+1),
                RX1_MFB_META    => s_rx_mfb_meta   (s)(2*i+1),
                RX1_MFB_SOF     => s_rx_mfb_sof    (s)(2*i+1),
                RX1_MFB_EOF     => s_rx_mfb_eof    (s)(2*i+1),
                RX1_MFB_SOF_POS => s_rx_mfb_sof_pos(s)(2*i+1),
                RX1_MFB_EOF_POS => s_rx_mfb_eof_pos(s)(2*i+1),
                RX1_MFB_SRC_RDY => s_rx_mfb_src_rdy(s)(2*i+1),
                RX1_MFB_DST_RDY => s_rx_mfb_dst_rdy(s)(2*i+1),

                TX_MVB_HDR      => s_rx_mvb_data   (s+1)(i),
                TX_MVB_PAYLOAD  => s_rx_mvb_payload(s+1)(i),
                TX_MVB_VLD      => s_rx_mvb_vld    (s+1)(i),
                TX_MVB_SRC_RDY  => s_rx_mvb_src_rdy(s+1)(i),
                TX_MVB_DST_RDY  => s_rx_mvb_dst_rdy(s+1)(i),
                TX_MFB_DATA     => s_rx_mfb_data   (s+1)(i),
                TX_MFB_META     => s_rx_mfb_meta   (s+1)(i),
                TX_MFB_SOF      => s_rx_mfb_sof    (s+1)(i),
                TX_MFB_EOF      => s_rx_mfb_eof    (s+1)(i),
                TX_MFB_SOF_POS  => s_rx_mfb_sof_pos(s+1)(i),
                TX_MFB_EOF_POS  => s_rx_mfb_eof_pos(s+1)(i),
                TX_MFB_SRC_RDY  => s_rx_mfb_src_rdy(s+1)(i),
                TX_MFB_DST_RDY  => s_rx_mfb_dst_rdy(s+1)(i)
            );

        end generate;
    end generate;

    TX_MVB_DATA    <= s_rx_mvb_data   (TREE_STAGES)(0);
    TX_MVB_PAYLOAD <= s_rx_mvb_payload(TREE_STAGES)(0);
    TX_MVB_VLD     <= s_rx_mvb_vld    (TREE_STAGES)(0);
    TX_MVB_SRC_RDY <= s_rx_mvb_src_rdy(TREE_STAGES)(0);

    s_rx_mvb_dst_rdy(TREE_STAGES)(0) <= TX_MVB_DST_RDY;

    TX_MFB_DATA    <= s_rx_mfb_data   (TREE_STAGES)(0);
    TX_MFB_META    <= s_rx_mfb_meta   (TREE_STAGES)(0);
    TX_MFB_SOF     <= s_rx_mfb_sof    (TREE_STAGES)(0);
    TX_MFB_EOF     <= s_rx_mfb_eof    (TREE_STAGES)(0);
    TX_MFB_SOF_POS <= s_rx_mfb_sof_pos(TREE_STAGES)(0);
    TX_MFB_EOF_POS <= s_rx_mfb_eof_pos(TREE_STAGES)(0);
    TX_MFB_SRC_RDY <= s_rx_mfb_src_rdy(TREE_STAGES)(0);

    s_rx_mfb_dst_rdy(TREE_STAGES)(0) <= TX_MFB_DST_RDY;

end architecture;
