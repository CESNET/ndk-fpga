-- mfb_splitter_flat.vhd: MFB+MVB bus splitter with a flat switch
-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- MFB+MVB bus splitter which routes to all its outputs in a single step.
--
-- Splits one input MVB+MFB stream into ``SPLITTER_OUTPUTS`` output streams.
--
-- .. warning::
--   Headers and frames are paired by order, not by content. The k-th frame on
--   RX MFB belongs to the k-th header that has ``RX_MVB_PAYLOAD(i)='1'``. A
--   header with ``'0'`` takes no frame.
--
-- **How it works**
--
-- Headers and payload are routed by two halves of this component, kept in step
-- by the switch FIFO.
--
-- The MVB half is a plain demultiplexer. ``RX_MVB_SWITCH`` says which output
-- each header goes to, so the header is written into that output's MVB FIFO.
-- Every header that announces a payload also writes its output number into the
-- switch FIFO. That FIFO holds one item per packet, in the order the packets
-- arrive on MFB.
--
-- The MFB half follows the switch FIFO. A word may carry one packet per Region,
-- so it takes as many items as the word has SOFs. Each Region is handed the
-- output number of the packet it belongs to, and
-- :vhdl:entity:`MFB_SPLITTER_SIMPLE_GEN` does the routing. A word only passes
-- once the FIFO holds an item for every SOF in it. Otherwise the MFB half would
-- route a packet whose header has not arrived yet.
--
entity MFB_SPLITTER_FLAT is
    generic (
        -- Number of splitter output streams, must be at least 2
        SPLITTER_OUTPUTS  : natural := 4;

        -- Number of MVB headers per word
        MVB_ITEMS         : natural := 2;
        -- Width of one MVB header in bits
        MVB_ITEM_WIDTH    : natural := 32;

        -- Number of Regions per MFB word
        MFB_REGIONS       : natural := 2;
        -- Number of Blocks per Region
        MFB_REG_SIZE      : natural := 1;
        -- Number of Items per Block
        MFB_BLOCK_SIZE    : natural := 8;
        -- Width of one MFB Item in bits
        MFB_ITEM_WIDTH    : natural := 32;

        -- Enable the input MFB FIFO. It holds the frame back until the header
        -- that says where to route it has arrived.
        IN_MFB_FIFO_EN    : boolean := false;
        -- Depth of the input MFB FIFO in words, only used when IN_MFB_FIFO_EN
        -- is true
        IN_MFB_FIFO_SIZE  : natural := 512;

        -- Depth of the output MVB FIFOs in words, minimum value is 2. They keep
        -- the outputs in step with the switch FIFO and cannot be turned off.
        OUT_MVB_FIFO_SIZE : natural := 8;

        -- Enable the output MFB FIFOs. A whole word is routed at once, so
        -- without them the slowest output holds up all the others.
        OUT_MFB_FIFO_EN   : boolean := false;
        -- Depth of the output MFB FIFOs in words, only used when
        -- OUT_MFB_FIFO_EN is true
        OUT_MFB_FIFO_SIZE : natural := 512;

        -- Architecture of the internal FIFOX_MULTI, "SHAKEDOWN" or "FULL"
        FIFOX_MULTI_ARCH  : string  := "SHAKEDOWN";

        -- Target device family
        DEVICE            : string  := "ULTRASCALE"
    );
    port (
        -- =====================================================================
        -- COMMON SIGNALS
        -- =====================================================================

        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- =====================================================================
        -- RX INTERFACE
        -- =====================================================================

        RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        -- Output select for each header, valid with RX_MVB_VLD
        RX_MVB_SWITCH  : in  std_logic_vector(MVB_ITEMS*log2(SPLITTER_OUTPUTS)-1 downto 0);
        -- The header is associated with a payload frame on MFB
        RX_MVB_PAYLOAD : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =====================================================================
        -- TX INTERFACES (per output port)
        -- =====================================================================

        TX_MVB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_PAYLOAD : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MVB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

        TX_MFB_DATA    : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
        TX_MFB_DST_RDY : in  std_logic_vector(SPLITTER_OUTPUTS-1 downto 0)
    );
end entity;

architecture FULL of MFB_SPLITTER_FLAT is

    -- =========================================================================
    --  CONSTANTS
    -- =========================================================================

    constant SOF_POS_WIDTH : natural := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH : natural := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));
    constant MFB_DATA_W    : natural := MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    -- Width of one switch item, it holds the number of an output stream
    constant SW_WIDTH      : natural := max(1,log2(SPLITTER_OUTPUTS));
    -- Number of SOFs a word can hold, and therefore of switch items the MFB
    -- half needs at once
    constant SOF_CNT_WIDTH : natural := log2(MFB_REGIONS+1);

    -- One output MVB FIFO item: the headers of a word, their payload flags and
    -- their valid flags
    constant MVB_FIFO_W    : natural := MVB_ITEMS*(MVB_ITEM_WIDTH+2);

    -- =========================================================================
    --  SIGNALS
    -- =========================================================================

    -- -------------------------------------------------------------------------
    -- Switch FIFO
    -- -------------------------------------------------------------------------

    signal switch_fifoxm_di       : std_logic_vector(MVB_ITEMS*SW_WIDTH-1 downto 0);
    signal switch_fifoxm_wr       : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal switch_fifoxm_full     : std_logic;
    signal switch_fifoxm_do       : std_logic_vector(MFB_REGIONS*SW_WIDTH-1 downto 0);

    -- RX MFB behind the optional input FIFO
    signal in_mfb_data    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal in_mfb_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal in_mfb_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal in_mfb_sof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
    signal in_mfb_eof_pos : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal in_mfb_src_rdy : std_logic;
    signal in_mfb_dst_rdy : std_logic;

    signal switch_fifoxm_do_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(SW_WIDTH-1 downto 0);
    signal switch_fifoxm_rd       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal switch_fifoxm_empty    : std_logic_vector(MFB_REGIONS-1 downto 0);
    -- Empty flags with a zero appended. Index zero then means "no item is
    -- needed at all" and reads as not empty.
    signal switch_fifoxm_empty_sh : std_logic_vector(MFB_REGIONS+1-1 downto 0);

    -- -------------------------------------------------------------------------
    -- MFB sending
    -- -------------------------------------------------------------------------

    -- Number of SOFs before each Region, and the switch each Region belongs to
    signal rx_mfb_sof_cnt     : u_array_t(MFB_REGIONS+1-1 downto 0)(SOF_CNT_WIDTH-1 downto 0);
    signal rx_mfb_sel         : slv_array_t(MFB_REGIONS-1 downto 0)(SW_WIDTH-1 downto 0);
    signal rx_mfb_sel_ser     : std_logic_vector(MFB_REGIONS*SW_WIDTH-1 downto 0);

    signal can_send_whole     : std_logic;
    signal mfb_spl_rx_src_rdy : std_logic;
    signal mfb_spl_rx_dst_rdy : std_logic;

    -- Splitter outputs, before the optional output FIFOs
    signal spl_mfb_data    : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_DATA_W-1 downto 0);
    signal spl_mfb_sof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal spl_mfb_eof     : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
    signal spl_mfb_sof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal spl_mfb_eof_pos : slv_array_t     (SPLITTER_OUTPUTS-1 downto 0)(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal spl_mfb_src_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal spl_mfb_dst_rdy : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);

    -- -------------------------------------------------------------------------
    -- MVB output FIFOs
    -- -------------------------------------------------------------------------

    signal rx_mvb_vld_out      : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
    signal mvb_out_fifox_di    : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(MVB_FIFO_W-1 downto 0);
    signal mvb_out_fifox_wr    : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal mvb_out_fifox_full  : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal mvb_out_fifox_do    : slv_array_t(SPLITTER_OUTPUTS-1 downto 0)(MVB_FIFO_W-1 downto 0);
    signal mvb_out_fifox_rd    : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal mvb_out_fifox_empty : std_logic_vector(SPLITTER_OUTPUTS-1 downto 0);
    signal mvb_out_fifox_ready : std_logic;

    signal rx_mvb_switch_arr : slv_array_t(MVB_ITEMS-1 downto 0)(SW_WIDTH-1 downto 0);

begin

    assert (SPLITTER_OUTPUTS >= 2)
        report "MFB_SPLITTER_FLAT: Use SPLITTER_OUTPUTS of 2 or more."
        severity failure;

    rx_mvb_switch_arr <= slv_array_deser(RX_MVB_SWITCH,MVB_ITEMS);

    -- No header may leave, and no switch may be written, unless every output
    -- MVB FIFO can take one. A header and its switch item have to go in
    -- together, otherwise the two halves would disagree about the order.
    mvb_out_fifox_ready <= '1' when (nor mvb_out_fifox_full) = '1' else '0';

    -- =========================================================================
    --  1. SWITCH FIFO
    -- =========================================================================
    -- Holds one item per packet: the number of the output that packet goes to,
    -- in arrival order.

    switch_fifoxm_in_g : for i in 0 to MVB_ITEMS-1 generate
        switch_fifoxm_di((i+1)*SW_WIDTH-1 downto i*SW_WIDTH) <= rx_mvb_switch_arr(i);

        -- Only a header that really arrives, and really has a payload, adds a
        -- switch for the MFB half.
        switch_fifoxm_wr(i) <= RX_MVB_SRC_RDY
                               and RX_MVB_VLD(i)
                               and RX_MVB_PAYLOAD(i)
                               and mvb_out_fifox_ready;
    end generate;

    switch_fifoxm_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH       => SW_WIDTH,
        ITEMS            => MVB_ITEMS*2*OUT_MVB_FIFO_SIZE,
        WRITE_PORTS      => MVB_ITEMS,
        READ_PORTS       => MFB_REGIONS,
        RAM_TYPE         => "AUTO",
        SAFE_READ_MODE   => true,
        DEVICE           => DEVICE,
        FIFOX_MULTI_ARCH => FIFOX_MULTI_ARCH
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        DI    => switch_fifoxm_di,
        WR    => switch_fifoxm_wr,
        FULL  => switch_fifoxm_full,
        DO    => switch_fifoxm_do,
        RD    => switch_fifoxm_rd,
        EMPTY => switch_fifoxm_empty
    );

    switch_fifoxm_do_arr <= slv_array_deser(switch_fifoxm_do,MFB_REGIONS);

    -- =========================================================================
    --  OPTIONAL INPUT MFB FIFO
    -- =========================================================================
    -- A source may only put the header out once the frame has ended. This FIFO
    -- holds the frame until its switch is in the switch FIFO.

    in_mfb_fifo_en_g : if (IN_MFB_FIFO_EN) generate
        in_mfb_fifo_i : entity work.MFB_FIFOX
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REG_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,
            FIFO_DEPTH  => IN_MFB_FIFO_SIZE,
            RAM_TYPE    => "AUTO",
            DEVICE      => DEVICE
        )
        port map (
            CLK        => CLK,
            RST        => RESET,

            RX_DATA    => RX_MFB_DATA,
            RX_SOF_POS => RX_MFB_SOF_POS,
            RX_EOF_POS => RX_MFB_EOF_POS,
            RX_SOF     => RX_MFB_SOF,
            RX_EOF     => RX_MFB_EOF,
            RX_SRC_RDY => RX_MFB_SRC_RDY,
            RX_DST_RDY => RX_MFB_DST_RDY,

            TX_DATA    => in_mfb_data,
            TX_SOF_POS => in_mfb_sof_pos,
            TX_EOF_POS => in_mfb_eof_pos,
            TX_SOF     => in_mfb_sof,
            TX_EOF     => in_mfb_eof,
            TX_SRC_RDY => in_mfb_src_rdy,
            TX_DST_RDY => in_mfb_dst_rdy
        );
    else generate
        in_mfb_data    <= RX_MFB_DATA;
        in_mfb_sof_pos <= RX_MFB_SOF_POS;
        in_mfb_eof_pos <= RX_MFB_EOF_POS;
        in_mfb_sof     <= RX_MFB_SOF;
        in_mfb_eof     <= RX_MFB_EOF;
        in_mfb_src_rdy <= RX_MFB_SRC_RDY;
        RX_MFB_DST_RDY <= in_mfb_dst_rdy;
    end generate;

    -- One item is taken for every SOF that leaves in this word.
    switch_fifoxm_rd_g : for i in 0 to MFB_REGIONS-1 generate
        switch_fifoxm_rd(i) <= '1' when (can_send_whole = '1'
                                         and i < rx_mfb_sof_cnt(MFB_REGIONS)
                                         and in_mfb_src_rdy = '1'
                                         and mfb_spl_rx_dst_rdy = '1') else
                               '0';
    end generate;

    switch_fifoxm_empty_sh <= switch_fifoxm_empty & '0';

    -- =========================================================================
    --  2. MFB SENDING
    -- =========================================================================

    -- Count the SOFs before each Region, and give every Region the switch of the
    -- packet it belongs to. A Region without an SOF of its own continues the
    -- packet that started earlier in the word. It takes that packet's switch.
    switch_dist_pr : process (all)
        variable cnt : natural;
    begin
        for i in 0 to MFB_REGIONS loop
            cnt := 0;
            for e in 0 to i-1 loop
                if (in_mfb_sof(e) = '1') then
                    cnt := cnt + 1;
                end if;
            end loop;
            rx_mfb_sof_cnt(i) <= to_unsigned(cnt,SOF_CNT_WIDTH);
        end loop;

        rx_mfb_sel <= (others => switch_fifoxm_do_arr(0));
        for i in 0 to MFB_REGIONS-1 loop
            rx_mfb_sel(i) <= switch_fifoxm_do_arr(to_integer(rx_mfb_sof_cnt(i)));
        end loop;
    end process;

    rx_mfb_sel_ser <= slv_array_ser(rx_mfb_sel);

    -- The word may only pass once the switch FIFO holds an item for every SOF.
    can_send_whole <= '1' when (switch_fifoxm_empty_sh(to_integer(rx_mfb_sof_cnt(MFB_REGIONS))) = '0') else '0';

    mfb_spl_rx_src_rdy <= '1' when (can_send_whole = '1' and in_mfb_src_rdy = '1') else '0';
    in_mfb_dst_rdy     <= '1' when (can_send_whole = '1' and mfb_spl_rx_dst_rdy = '1') else '0';

    mfb_splitter_i : entity work.MFB_SPLITTER_SIMPLE_GEN
    generic map (
        SPLITTER_OUTPUTS => SPLITTER_OUTPUTS,
        REGIONS          => MFB_REGIONS,
        REGION_SIZE      => MFB_REG_SIZE,
        BLOCK_SIZE       => MFB_BLOCK_SIZE,
        ITEM_WIDTH       => MFB_ITEM_WIDTH,
        META_WIDTH       => 0,
        DEVICE           => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MFB_SEL     => rx_mfb_sel_ser,
        RX_MFB_DATA    => in_mfb_data,
        RX_MFB_META    => (others => '0'),
        RX_MFB_SOF     => in_mfb_sof,
        RX_MFB_EOF     => in_mfb_eof,
        RX_MFB_SOF_POS => in_mfb_sof_pos,
        RX_MFB_EOF_POS => in_mfb_eof_pos,
        RX_MFB_SRC_RDY => mfb_spl_rx_src_rdy,
        RX_MFB_DST_RDY => mfb_spl_rx_dst_rdy,

        TX_MFB_DATA    => spl_mfb_data,
        TX_MFB_META    => open,
        TX_MFB_SOF     => spl_mfb_sof,
        TX_MFB_EOF     => spl_mfb_eof,
        TX_MFB_SOF_POS => spl_mfb_sof_pos,
        TX_MFB_EOF_POS => spl_mfb_eof_pos,
        TX_MFB_SRC_RDY => spl_mfb_src_rdy,
        TX_MFB_DST_RDY => spl_mfb_dst_rdy
    );

    -- =========================================================================
    --  3. OPTIONAL OUTPUT MFB FIFOS
    -- =========================================================================
    -- A whole word is routed at once, so every output has to take its share in
    -- the same cycle. A FIFO per output delays that until the FIFO is full.

    out_mfb_fifo_g : for i in 0 to SPLITTER_OUTPUTS-1 generate
        out_mfb_fifo_en_g : if (OUT_MFB_FIFO_EN) generate
            mfb_fifo_i : entity work.MFB_FIFOX
            generic map (
                REGIONS     => MFB_REGIONS,
                REGION_SIZE => MFB_REG_SIZE,
                BLOCK_SIZE  => MFB_BLOCK_SIZE,
                ITEM_WIDTH  => MFB_ITEM_WIDTH,
                FIFO_DEPTH  => OUT_MFB_FIFO_SIZE,
                RAM_TYPE    => "AUTO",
                DEVICE      => DEVICE
            )
            port map (
                CLK        => CLK,
                RST        => RESET,

                RX_DATA    => spl_mfb_data(i),
                RX_SOF_POS => spl_mfb_sof_pos(i),
                RX_EOF_POS => spl_mfb_eof_pos(i),
                RX_SOF     => spl_mfb_sof(i),
                RX_EOF     => spl_mfb_eof(i),
                RX_SRC_RDY => spl_mfb_src_rdy(i),
                RX_DST_RDY => spl_mfb_dst_rdy(i),

                TX_DATA    => TX_MFB_DATA(i),
                TX_SOF_POS => TX_MFB_SOF_POS(i),
                TX_EOF_POS => TX_MFB_EOF_POS(i),
                TX_SOF     => TX_MFB_SOF(i),
                TX_EOF     => TX_MFB_EOF(i),
                TX_SRC_RDY => TX_MFB_SRC_RDY(i),
                TX_DST_RDY => TX_MFB_DST_RDY(i)
            );
        else generate
            TX_MFB_DATA(i)     <= spl_mfb_data(i);
            TX_MFB_SOF_POS(i)  <= spl_mfb_sof_pos(i);
            TX_MFB_EOF_POS(i)  <= spl_mfb_eof_pos(i);
            TX_MFB_SOF(i)      <= spl_mfb_sof(i);
            TX_MFB_EOF(i)      <= spl_mfb_eof(i);
            TX_MFB_SRC_RDY(i)  <= spl_mfb_src_rdy(i);
            spl_mfb_dst_rdy(i) <= TX_MFB_DST_RDY(i);
        end generate;
    end generate;

    -- =========================================================================
    --  4. MVB SENDING
    -- =========================================================================
    -- Every output gets the whole word of headers, with only its own items
    -- marked valid.

    rx_mvb_vld_g : for i in 0 to SPLITTER_OUTPUTS-1 generate
        rx_mvb_vld_item_g : for e in 0 to MVB_ITEMS-1 generate
            rx_mvb_vld_out(i)(e) <= '1' when (unsigned(rx_mvb_switch_arr(e)) = i
                                              and RX_MVB_VLD(e) = '1'
                                              and RX_MVB_SRC_RDY = '1') else
                                    '0';
        end generate;

        mvb_out_fifox_di(i)(MVB_FIFO_W-1 downto MVB_ITEMS*2) <= RX_MVB_DATA;
        mvb_out_fifox_di(i)(MVB_ITEMS*2-1 downto MVB_ITEMS)  <= RX_MVB_PAYLOAD;
        mvb_out_fifox_di(i)(MVB_ITEMS-1 downto 0)            <= rx_mvb_vld_out(i);

        -- A word is written only into the outputs it carries items for, and
        -- never unless every output could take one. The FIFOs therefore stay
        -- in step with the switch FIFO.
        mvb_out_fifox_wr(i) <= '1' when (RX_MVB_SRC_RDY = '1'
                                         and (or rx_mvb_vld_out(i)) = '1'
                                         and mvb_out_fifox_ready = '1'
                                         and switch_fifoxm_full = '0') else
                               '0';

        mvb_out_fifox_i : entity work.FIFOX
        generic map (
            DATA_WIDTH => MVB_FIFO_W,
            ITEMS      => OUT_MVB_FIFO_SIZE,
            RAM_TYPE   => "AUTO",
            DEVICE     => DEVICE
        )
        port map (
            CLK   => CLK,
            RESET => RESET,

            DI    => mvb_out_fifox_di(i),
            WR    => mvb_out_fifox_wr(i),
            FULL  => mvb_out_fifox_full(i),

            DO    => mvb_out_fifox_do(i),
            RD    => mvb_out_fifox_rd(i),
            EMPTY => mvb_out_fifox_empty(i)
        );

        TX_MVB_DATA(i)      <= mvb_out_fifox_do(i)(MVB_FIFO_W-1 downto MVB_ITEMS*2);
        TX_MVB_PAYLOAD(i)   <= mvb_out_fifox_do(i)(MVB_ITEMS*2-1 downto MVB_ITEMS);
        TX_MVB_VLD(i)       <= mvb_out_fifox_do(i)(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY(i)   <= not mvb_out_fifox_empty(i);
        mvb_out_fifox_rd(i) <= TX_MVB_DST_RDY(i);
    end generate;

    RX_MVB_DST_RDY <= '1' when (switch_fifoxm_full = '0' and mvb_out_fifox_ready = '1') else '0';

end architecture;
