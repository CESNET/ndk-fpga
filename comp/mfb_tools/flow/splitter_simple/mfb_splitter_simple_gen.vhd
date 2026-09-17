-- mfb_splitter_simple_gen.vhd: MFB bus splitter with generic number of outputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;


-- =========================================================================
--  Description
-- =========================================================================

-- This is a 1:N MFB splitter.
-- ``RX_MFB_SEL`` selects the output for each frame. The whole RX word is sent
-- to every output in the same clock cycle. Each output gets the word with the
-- SOFs and EOFs of the other outputs masked out. ``TX_MFB_SRC_RDY`` of an
-- output stays low when the word carries no frame for that output. The latency
-- is one clock cycle.
--
-- .. warning::
--   An RX word is taken only once every output can accept it, so the slowest
--   output stops all the others.
--
entity MFB_SPLITTER_SIMPLE_GEN is
    generic (
        -- Number of splitter outputs.
        SPLITTER_OUTPUTS   : integer := 8;
        -- Number of Regions in a word.
        REGIONS            : integer := 4;
        -- Number of Blocks in a Region.
        REGION_SIZE        : integer := 8;
        -- Number of Items in a Block.
        BLOCK_SIZE         : integer := 8;
        -- Width  of one Item (in bits).
        ITEM_WIDTH         : integer := 8;
        -- Width of MFB metadata (in bits).
        META_WIDTH         : integer := 1;

        -- Input PIPEs enable for all 1:2 Splitters.
        -- Input registers are created when this is set to false.
        -- IN_PIPE_EN      : boolean := false;

        -- Output PIPE enable for all 1:2 Splitters.
        -- Output register are created when this is set to false.
        -- OUT_PIPE_EN     : boolean := true;

        -- FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE : string := "AGILEX"
    );
    port (
        -- =====================================================================
        -- Clock and Reset
        -- =====================================================================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX interface
        -- =====================================================================

        -- One select bit for each stage (and for each region ofc), bit RX_MFB_SEL(0)(x) is for Stage 0, and so on.
        -- Expected to be valid with SOF!
        RX_MFB_SEL     : in  std_logic_vector(REGIONS*max(1,log2(SPLITTER_OUTPUTS))-1 downto 0);
        RX_MFB_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- Valid whenever, metadata is split by words
        RX_MFB_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- TX interface
        -- =====================================================================

        TX_MFB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
        -- Valid whenever, metadata is split by words
        TX_MFB_META    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*META_WIDTH-1 downto 0) := (others => (others => '0'));
        TX_MFB_SOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SPLITTER_SIMPLE_GEN is

    -- =========================================================================
    --  CONSTANTS
    -- =========================================================================

    constant SEL_WIDTH     : natural := max(1,log2(SPLITTER_OUTPUTS));
    constant SOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(REGION_SIZE*BLOCK_SIZE));
    constant DATA_WIDTH    : natural := REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;

    -- =========================================================================
    --  SIGNALS
    -- =========================================================================

    signal rx_sel_arr     : slv_array_t(REGIONS-1 downto 0)(SEL_WIDTH-1 downto 0);
    signal rx_sof_pos_arr : slv_array_t(REGIONS-1 downto 0)(SOF_POS_WIDTH-1 downto 0);
    signal rx_eof_pos_arr : slv_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    -- Bit r is '1' when the SOF and the EOF of Region r belong to one frame
    signal sof_b4_eof     : std_logic_vector(REGIONS-1 downto 0);
    signal sof_pos_cmp    : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);
    signal eof_pos_cmp    : u_array_t(REGIONS-1 downto 0)(EOF_POS_WIDTH-1 downto 0);

    -- The masked control signals of each output, before the output registers
    signal new_sof        : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
    signal new_eof        : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
    signal new_src_rdy    : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

    -- need_eof(o)(r) is '1' when the last SOF before Region r selected output o.
    -- Bit REGIONS is the value that the next word starts from.
    signal need_eof       : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS downto 0);
    -- pkt_cont(o)(r) is '1' when a frame of output o is open in front of Region r.
    -- Bit REGIONS is the value that the next word starts from.
    signal pkt_cont       : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS downto 0);
    signal need_eof_reg   : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal pkt_cont_reg   : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

    signal new_dst_rdy    : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal rx_dst_rdy     : std_logic;
    -- An RX word is taken in this clock cycle
    signal word_vld       : std_logic;

    signal tx_data_reg    : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal tx_meta_reg    : std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    signal tx_sof_pos_reg : std_logic_vector(REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal tx_eof_pos_reg : std_logic_vector(REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal tx_sof_reg     : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
    signal tx_eof_reg     : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(REGIONS-1 downto 0);
    signal tx_src_rdy_reg : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

begin

    -- A single output takes every frame, so there is nothing to mask.
    bypass_g : if (SPLITTER_OUTPUTS = 1) generate

        TX_MFB_DATA(0)    <= RX_MFB_DATA;
        TX_MFB_META(0)    <= RX_MFB_META;
        TX_MFB_SOF(0)     <= RX_MFB_SOF;
        TX_MFB_EOF(0)     <= RX_MFB_EOF;
        TX_MFB_SOF_POS(0) <= RX_MFB_SOF_POS;
        TX_MFB_EOF_POS(0) <= RX_MFB_EOF_POS;
        TX_MFB_SRC_RDY(0) <= RX_MFB_SRC_RDY;
        RX_MFB_DST_RDY    <= TX_MFB_DST_RDY(0);

    else generate

        rx_sel_arr     <= slv_array_deser(RX_MFB_SEL,REGIONS);
        rx_sof_pos_arr <= slv_array_deser(RX_MFB_SOF_POS,REGIONS);
        rx_eof_pos_arr <= slv_array_deser(RX_MFB_EOF_POS,REGIONS);

        -- =====================================================================
        --  1. SOF AND EOF MASKING
        -- =====================================================================

        -- With REGION_SIZE of 1 a frame always starts at the Region start, so
        -- the SOF is never after the EOF.
        sof_b4_eof_g : if (REGION_SIZE > 1) generate
            sof_b4_eof_r_g : for r in 0 to REGIONS-1 generate
                sof_pos_cmp(r) <= resize_right(unsigned(rx_sof_pos_arr(r)),EOF_POS_WIDTH);
                eof_pos_cmp(r) <= unsigned(rx_eof_pos_arr(r));
                sof_b4_eof(r)  <= '1' when (sof_pos_cmp(r) <= eof_pos_cmp(r)) else '0';
            end generate;
        else generate
            sof_b4_eof <= (others => '1');
        end generate;

        out_logic_g : for o in 0 to SPLITTER_OUTPUTS-1 generate

            need_eof(o)(0) <= need_eof_reg(o);
            pkt_cont(o)(0) <= pkt_cont_reg(o);

            region_g : for r in 0 to REGIONS-1 generate

                new_sof(o)(r) <= '1' when (RX_MFB_SOF(r) = '1' and unsigned(rx_sel_arr(r)) = o) else
                                 '0';

                -- An SOF sets this state for the output it selects and clears
                -- it for all the other outputs.
                need_eof(o)(r+1) <= new_sof(o)(r) when (RX_MFB_SOF(r) = '1') else
                                    need_eof(o)(r);

                -- When one Region holds both the SOF and the EOF of the same
                -- frame, the EOF belongs to the output of that SOF. Otherwise
                -- the EOF ends the frame that is already open.
                new_eof(o)(r) <= new_sof(o)(r) when (RX_MFB_SOF(r) = '1' and RX_MFB_EOF(r) = '1' and sof_b4_eof(r) = '1') else
                                 (need_eof(o)(r) and RX_MFB_EOF(r));

                pkt_cont(o)(r+1) <= (new_sof(o)(r) and not new_eof(o)(r) and not pkt_cont(o)(r)) or
                                    (new_sof(o)(r) and new_eof(o)(r) and pkt_cont(o)(r)) or
                                    (not new_sof(o)(r) and not new_eof(o)(r) and pkt_cont(o)(r));

            end generate;

            -- Output o gets the word when a frame of output o starts in it or
            -- continues through it.
            new_src_rdy(o) <= (or (new_sof(o) or pkt_cont(o)(REGIONS-1 downto 0))) and word_vld;

        end generate;

        -- =====================================================================
        --  2. HANDSHAKE
        -- =====================================================================
        -- An output is ready when its registered word is being taken, or when it
        -- holds no word. The RX word is taken only once all outputs are ready.

        new_dst_rdy_g : for o in 0 to SPLITTER_OUTPUTS-1 generate
            new_dst_rdy(o) <= TX_MFB_DST_RDY(o) or not tx_src_rdy_reg(o);
        end generate;

        rx_dst_rdy     <= and new_dst_rdy;
        RX_MFB_DST_RDY <= rx_dst_rdy;
        word_vld       <= RX_MFB_SRC_RDY and rx_dst_rdy;

        -- =====================================================================
        --  3. OUTPUT REGISTERS
        -- =====================================================================
        -- Every output gets the same word in the same clock cycle, so the
        -- payload is registered once. Only the masked control signals are kept
        -- per output.

        word_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (word_vld = '1') then
                    tx_data_reg    <= RX_MFB_DATA;
                    tx_meta_reg    <= RX_MFB_META;
                    tx_sof_pos_reg <= RX_MFB_SOF_POS;
                    tx_eof_pos_reg <= RX_MFB_EOF_POS;
                end if;
            end if;
        end process;

        out_reg_g : for o in 0 to SPLITTER_OUTPUTS-1 generate
            out_reg_p : process (CLK)
            begin
                if (rising_edge(CLK)) then
                    if (new_dst_rdy(o) = '1') then
                        tx_sof_reg(o)     <= new_sof(o);
                        tx_eof_reg(o)     <= new_eof(o);
                        tx_src_rdy_reg(o) <= new_src_rdy(o);
                    end if;
                    if (RESET = '1') then
                        tx_src_rdy_reg(o) <= '0';
                    end if;
                end if;
            end process;
        end generate;

        state_reg_p : process (CLK)
        begin
            if (rising_edge(CLK)) then
                if (RESET = '1') then
                    need_eof_reg <= (others => '0');
                    pkt_cont_reg <= (others => '0');
                elsif (word_vld = '1') then
                    for o in 0 to SPLITTER_OUTPUTS-1 loop
                        need_eof_reg(o) <= need_eof(o)(REGIONS);
                        pkt_cont_reg(o) <= pkt_cont(o)(REGIONS);
                    end loop;
                end if;
            end if;
        end process;

        tx_g : for o in 0 to SPLITTER_OUTPUTS-1 generate
            TX_MFB_DATA(o)    <= tx_data_reg;
            TX_MFB_META(o)    <= tx_meta_reg;
            TX_MFB_SOF(o)     <= tx_sof_reg(o);
            TX_MFB_EOF(o)     <= tx_eof_reg(o);
            TX_MFB_SOF_POS(o) <= tx_sof_pos_reg;
            TX_MFB_EOF_POS(o) <= tx_eof_pos_reg;
            TX_MFB_SRC_RDY(o) <= tx_src_rdy_reg(o);
        end generate;

    end generate;

end architecture;
