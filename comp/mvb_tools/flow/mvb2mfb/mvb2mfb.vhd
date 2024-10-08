-- mvb2mfb.vhd: MVB to MFB conversion
-- Copyright (C) 2023 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- Component MVB2MFB converts MVB ITEMs to MFB transactions. It is possible to
-- set different parameters for the input MVB bus and the output MFB bus.
-- However, there are several limiting conditions, see the description of
-- generics ports. MFB metadata are valid with each SOF.
entity MVB2MFB is
    generic(
        MVB_ITEMS       : natural := 4;
        -- MVB_ITEM_WIDTH must be a multiple of MFB_ITEM_WIDTH;
        -- MVB_ITEM_WIDTH must be >= MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH
        -- or MFB_ALIGNMENT must be = MFB_REGION_SIZE*MFB_BLOCK_SIZE
        MVB_ITEM_WIDTH  : natural := 536;

        MFB_REGIONS     : natural := 4;
        MFB_REGION_SIZE : natural := 8;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        -- Alignment of the start of MFB transactions in MFB ITEMs:
        -- Higher number => saving resources and better timing,
        -- lower number  => higher transmission efficiency.
        -- MFB_ALIGNMENT must be power of two; minimum value is MFB_BLOCK_SIZE,
        -- maximum value is MFB_REGION_SIZE*MFB_BLOCK_SIZE.
        MFB_ALIGNMENT   : natural := MFB_REGION_SIZE*MFB_BLOCK_SIZE;
        -- User metadata width in bits
        META_WIDTH      : natural := 12;
        -- FPGA device string (required for FIFO)
        DEVICE          : string := "AGILEX"
    );
    port(
        -- Clock input
        CLK            : in  std_logic;
        -- Reset input synchronized with CLK
        RESET          : in  std_logic;

        RX_MVB_DATA    : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_MVB_META    : in  std_logic_vector(MVB_ITEMS*META_WIDTH-1 downto 0);
        RX_MVB_VLD     : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        -- MFB metadata are valid with each SOF.
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MVB2MFB is

    constant MVB_BLOCK_W   : natural := MFB_ALIGNMENT*MFB_ITEM_WIDTH;
    constant MVB_BLOCKS    : natural := div_roundup(MVB_ITEM_WIDTH, MVB_BLOCK_W);
    constant END_POS       : natural := (MVB_ITEM_WIDTH mod MVB_BLOCK_W)/MFB_ITEM_WIDTH;
    constant END_POS_W     : natural := log2(MFB_ALIGNMENT);
    constant WRITE_PORTS   : natural := MVB_ITEMS*MVB_BLOCKS;
    constant READ_REGION_S : natural := (MFB_REGION_SIZE*MFB_BLOCK_SIZE)/MFB_ALIGNMENT;
    constant READ_PORTS    : natural := MFB_REGIONS*READ_REGION_S;

    constant FIFO_DEPTH    : natural := 32;
    constant FIFO_DATA_W   : natural := MVB_BLOCK_W+META_WIDTH+END_POS_W+1+1;

    signal rx_mvb_data_arr     : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal rx_mvb_data_ext_arr : slv_array_t(MVB_ITEMS-1 downto 0)(MVB_BLOCKS*MVB_BLOCK_W-1 downto 0);
    signal rx_mvb_meta_arr     : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH-1 downto 0);

    signal fifoxm_di_arr       : slv_array_t(WRITE_PORTS-1 downto 0)(FIFO_DATA_W-1 downto 0);
    signal fifoxm_wr           : std_logic_vector(WRITE_PORTS-1 downto 0);
    signal fifoxm_full         : std_logic;
    signal fifoxm_do           : std_logic_vector(READ_PORTS*FIFO_DATA_W-1 downto 0);
    signal fifoxm_do_arr       : slv_array_t(READ_PORTS-1 downto 0)(FIFO_DATA_W-1 downto 0);
    signal fifoxm_rd_mask      : std_logic_vector(READ_PORTS-1 downto 0);
    signal fifoxm_rd           : std_logic_vector(READ_PORTS-1 downto 0);
    signal fifoxm_empty        : std_logic_vector(READ_PORTS-1 downto 0);

    signal fifoxm_data_arr     : slv_array_t(READ_PORTS-1 downto 0)(MVB_BLOCK_W-1 downto 0);
    signal fifoxm_meta_arr     : slv_array_t(READ_PORTS-1 downto 0)(META_WIDTH-1 downto 0);
    signal fifoxm_end_pos_arr  : slv_array_t(READ_PORTS-1 downto 0)(END_POS_W-1 downto 0);
    signal fifoxm_start        : std_logic_vector(READ_PORTS-1 downto 0);
    signal fifoxm_end          : std_logic_vector(READ_PORTS-1 downto 0);
    signal fifoxm_vld          : std_logic_vector(READ_PORTS-1 downto 0);
    signal fifoxm_word_vld     : std_logic;
    signal fifoxm_sof_sel      : u_array_t(MFB_REGIONS-1 downto 0)(log2(READ_PORTS)-1 downto 0);
    signal fifoxm_eof_sel      : u_array_t(MFB_REGIONS-1 downto 0)(log2(READ_PORTS)-1 downto 0);

    signal mfb_data            : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal mfb_meta_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(META_WIDTH-1 downto 0);
    signal mfb_meta            : std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
    signal mfb_sof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_eof             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mfb_sof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(READ_REGION_S))-1 downto 0);
    signal mfb_sof_pos_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(READ_REGION_S))-1 downto 0);
    signal mfb_eof_pos_hi_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(READ_REGION_S))-1 downto 0);
    signal mfb_eof_pos_lo_arr  : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(MFB_ALIGNMENT))-1 downto 0);
    signal mfb_eof_pos_arr     : slv_array_t(MFB_REGIONS-1 downto 0)(max(1,log2(READ_REGION_S*MFB_ALIGNMENT))-1 downto 0);
    signal mfb_eof_pos         : std_logic_vector(MFB_REGIONS*max(1,log2(READ_REGION_S*MFB_ALIGNMENT))-1 downto 0);
    signal mfb_src_rdy         : std_logic;
    signal mfb_dst_rdy         : std_logic;

    signal rec_mfb_data        : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal rec_mfb_meta        : std_logic_vector(MFB_REGIONS*META_WIDTH-1 downto 0);
    signal rec_mfb_sof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rec_mfb_eof         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rec_mfb_sof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal rec_mfb_eof_pos     : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal rec_mfb_src_rdy     : std_logic;

    signal dbg_rx_pkt_cnt      : unsigned(64-1 downto 0);
    signal dbg_tx_pkt_cnt      : unsigned(64-1 downto 0);

begin

    assert ((MVB_ITEM_WIDTH >= MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH) or (MFB_ALIGNMENT = MFB_REGION_SIZE*MFB_BLOCK_SIZE))
        report "MVB2MFB: MVB_ITEM_WIDTH must be >= MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH or MFB_ALIGNMENT must be = MFB_REGION_SIZE*MFB_BLOCK_SIZE!"
        severity failure;

    assert ((MVB_ITEM_WIDTH mod MFB_ITEM_WIDTH) = 0)
        report "MVB2MFB: MVB_ITEM_WIDTH must be a multiple of MFB_ITEM_WIDTH!"
        severity failure;

    assert ((MFB_ALIGNMENT <= MFB_REGION_SIZE*MFB_BLOCK_SIZE) and (MFB_ALIGNMENT >= MFB_BLOCK_SIZE))
        report "MVB2MFB: MFB_ALIGNMENT must be <= MFB_REGION_SIZE*MFB_BLOCK_SIZE and >= MFB_BLOCK_SIZE!"
        severity failure;

    RX_MVB_DST_RDY <= not fifoxm_full;

    rx_mvb_data_arr <= slv_array_deser(RX_MVB_DATA, MVB_ITEMS);
    rx_mvb_meta_arr <= slv_array_deser(RX_MVB_META, MVB_ITEMS);

    fdi_pack_g: for ii in 0 to MVB_ITEMS-1 generate
        rx_mvb_data_ext_arr(ii) <= std_logic_vector(resize(unsigned(rx_mvb_data_arr(ii)), (MVB_BLOCKS*MVB_BLOCK_W)));

        fdi_pack_g2: for bb in 0 to MVB_BLOCKS-1 generate
            fifoxm_di_arr(ii*MVB_BLOCKS+bb)(MVB_BLOCK_W-1 downto 0) <= rx_mvb_data_ext_arr(ii)((bb+1)*MVB_BLOCK_W-1 downto bb*MVB_BLOCK_W);
            fifoxm_di_arr(ii*MVB_BLOCKS+bb)(MVB_BLOCK_W+META_WIDTH-1 downto MVB_BLOCK_W)                      <= rx_mvb_meta_arr(ii);
            fifoxm_di_arr(ii*MVB_BLOCKS+bb)(MVB_BLOCK_W+META_WIDTH+END_POS_W-1 downto MVB_BLOCK_W+META_WIDTH) <= std_logic_vector(to_unsigned(END_POS, END_POS_W) - 1); -- position of end in block
            fifoxm_di_arr(ii*MVB_BLOCKS+bb)(MVB_BLOCK_W+META_WIDTH+END_POS_W)                                 <= '1' when (bb = 0) else '0'; -- start block
            fifoxm_di_arr(ii*MVB_BLOCKS+bb)(MVB_BLOCK_W+META_WIDTH+END_POS_W+1)                               <= '1' when (bb = MVB_BLOCKS-1) else '0'; -- end block

            fifoxm_wr(ii*MVB_BLOCKS+bb) <= RX_MVB_VLD(ii) and RX_MVB_SRC_RDY;
        end generate;
    end generate;

    fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH     => FIFO_DATA_W,
        ITEMS          => max(WRITE_PORTS, READ_PORTS)*FIFO_DEPTH,
        WRITE_PORTS    => WRITE_PORTS,
        READ_PORTS     => READ_PORTS,
        RAM_TYPE       => "AUTO",
        SAFE_READ_MODE => False,
        DEVICE         => DEVICE
    )
    port map(
        CLK    => CLK,
        RESET  => RESET,

        DI     => slv_array_ser(fifoxm_di_arr),
        WR     => fifoxm_wr,
        FULL   => fifoxm_full,

        DO     => fifoxm_do,
        RD     => fifoxm_rd,
        EMPTY  => fifoxm_empty
    );

    fifoxm_do_arr <= slv_array_deser(fifoxm_do, READ_PORTS);

    fdo_unpack_g: for rr in 0 to READ_PORTS-1 generate
        fifoxm_data_arr(rr)    <= fifoxm_do_arr(rr)(MVB_BLOCK_W-1 downto 0);
        fifoxm_meta_arr(rr)    <= fifoxm_do_arr(rr)(MVB_BLOCK_W+META_WIDTH-1 downto MVB_BLOCK_W);
        fifoxm_end_pos_arr(rr) <= fifoxm_do_arr(rr)(MVB_BLOCK_W+META_WIDTH+END_POS_W-1 downto MVB_BLOCK_W+META_WIDTH);
        fifoxm_start(rr)       <= fifoxm_do_arr(rr)(MVB_BLOCK_W+META_WIDTH+END_POS_W) and not fifoxm_empty(rr);
        fifoxm_end(rr)         <= fifoxm_do_arr(rr)(MVB_BLOCK_W+META_WIDTH+END_POS_W+1) and not fifoxm_empty(rr);

        fifoxm_vld(rr) <= not fifoxm_empty(rr);
    end generate;

    fifoxm_word_vld <= nor fifoxm_empty;

    process (all)
    begin
        fifoxm_rd_mask <= (others => '0');

        for rr in READ_PORTS-1 downto 0 loop
            -- read all bits from last END in the word
            if (fifoxm_empty(rr) = '0' and fifoxm_end(rr) = '1') then
                fifoxm_rd_mask(rr downto 0) <= (others => '1');
                exit;
            end if;
        end loop;

        -- OR read whole valid word
        if (fifoxm_word_vld = '1') then
            fifoxm_rd_mask <= (others => '1');
        end if;
    end process;

    fifoxm_rd <= fifoxm_rd_mask and mfb_dst_rdy;

    mfb_xof_g: for rr in 0 to MFB_REGIONS-1 generate
        mfb_sof(rr) <= or fifoxm_start((rr+1)*READ_REGION_S-1 downto rr*READ_REGION_S);
        mfb_eof(rr) <= or fifoxm_end((rr+1)*READ_REGION_S-1 downto rr*READ_REGION_S);

        enc_g: if (READ_REGION_S > 1) generate
            sof_enc_i : entity work.GEN_ENC
            generic map (
                ITEMS => READ_REGION_S
            )
            port map (
                DI    => fifoxm_start((rr+1)*READ_REGION_S-1 downto rr*READ_REGION_S),
                ADDR  => mfb_sof_pos_arr(rr)
            );

            eof_enc_i : entity work.GEN_ENC
            generic map (
                ITEMS => READ_REGION_S
            )
            port map (
                DI    => fifoxm_end((rr+1)*READ_REGION_S-1 downto rr*READ_REGION_S),
                ADDR  => mfb_eof_pos_hi_arr(rr)
            );

            fifoxm_sof_sel(rr) <= to_unsigned(rr, log2(MFB_REGIONS)) & unsigned(mfb_sof_pos_arr(rr));
            fifoxm_eof_sel(rr) <= to_unsigned(rr, log2(MFB_REGIONS)) & unsigned(mfb_eof_pos_hi_arr(rr));
        else generate
            mfb_sof_pos_arr(rr) <= (others => '0');
            fifoxm_sof_sel(rr) <= to_unsigned(rr, log2(MFB_REGIONS));
            fifoxm_eof_sel(rr) <= to_unsigned(rr, log2(MFB_REGIONS));
        end generate;

        mfb_meta_arr(rr) <= fifoxm_meta_arr(to_integer(fifoxm_sof_sel(rr)));

        eof_pos_lo_g: if (MFB_ALIGNMENT > 1) generate
            mfb_eof_pos_lo_arr(rr) <= fifoxm_end_pos_arr(to_integer(fifoxm_eof_sel(rr)));
        else generate
            mfb_eof_pos_lo_arr(rr) <= (others => '0');
        end generate;

        eof_pos_g: if (READ_REGION_S > 1) generate
            mfb_eof_pos_arr(rr) <= mfb_eof_pos_hi_arr(rr) & mfb_eof_pos_lo_arr(rr);
        else generate
            mfb_eof_pos_arr(rr) <= mfb_eof_pos_lo_arr(rr);
        end generate;
    end generate;

    mfb_data    <= slv_array_ser(fifoxm_data_arr);
    mfb_meta    <= slv_array_ser(mfb_meta_arr);
    mfb_sof_pos <= slv_array_ser(mfb_sof_pos_arr);
    mfb_eof_pos <= slv_array_ser(mfb_eof_pos_arr);
    mfb_src_rdy <= or fifoxm_rd_mask;

    mfb_reconf_i : entity work.MFB_RECONFIGURATOR
    generic map(
        RX_REGIONS            => MFB_REGIONS,
        RX_REGION_SIZE        => READ_REGION_S,
        RX_BLOCK_SIZE         => MFB_ALIGNMENT,
        RX_ITEM_WIDTH         => MFB_ITEM_WIDTH,
        TX_REGIONS            => MFB_REGIONS,
        TX_REGION_SIZE        => MFB_REGION_SIZE,
        TX_BLOCK_SIZE         => MFB_BLOCK_SIZE,
        TX_ITEM_WIDTH         => MFB_ITEM_WIDTH,
        META_WIDTH            => META_WIDTH,
        FIFO_SIZE             => 32,
        FRAMES_OVER_TX_BLOCK  => 1,
        FRAMES_OVER_TX_REGION => 1,
        DEVICE                => DEVICE
    )
    port map(
        CLK        => CLK,
        RESET      => RESET,

        RX_DATA    => mfb_data,
        RX_META    => mfb_meta,
        RX_SOF     => mfb_sof,
        RX_EOF     => mfb_eof,
        RX_SOF_POS => mfb_sof_pos,
        RX_EOF_POS => mfb_eof_pos,
        RX_SRC_RDY => mfb_src_rdy,
        RX_DST_RDY => mfb_dst_rdy,

        TX_DATA    => rec_mfb_data,
        TX_META    => rec_mfb_meta,
        TX_SOF     => rec_mfb_sof,
        TX_EOF     => rec_mfb_eof,
        TX_SOF_POS => rec_mfb_sof_pos,
        TX_EOF_POS => rec_mfb_eof_pos,
        TX_SRC_RDY => rec_mfb_src_rdy,
        TX_DST_RDY => TX_MFB_DST_RDY
    );

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                TX_MFB_DATA    <= rec_mfb_data;
                TX_MFB_META    <= rec_mfb_meta;
                TX_MFB_SOF     <= rec_mfb_sof;
                TX_MFB_EOF     <= rec_mfb_eof;
                TX_MFB_SOF_POS <= rec_mfb_sof_pos;
                TX_MFB_EOF_POS <= rec_mfb_eof_pos;
                TX_MFB_SRC_RDY <= rec_mfb_src_rdy;
            end if;
            if (RESET = '1') then
                TX_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- =========================================================================
    -- DEBUG LOGIC
    -- =========================================================================

    --pragma synthesis_off
    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_rx_pkt_cnt <= (others => '0');
            elsif (RX_MVB_SRC_RDY = '1' and RX_MVB_DST_RDY = '1') then
                for i in 0 to MVB_ITEMS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + RX_MVB_VLD(i);
                end loop;
                dbg_rx_pkt_cnt <= dbg_rx_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;

    process (CLK)
        variable dbg_pkt_cnt_v : unsigned(63 downto 0);
    begin
        dbg_pkt_cnt_v := (others => '0');
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                dbg_tx_pkt_cnt <= (others => '0');
            elsif (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                for i in 0 to MFB_REGIONS-1 loop
                    dbg_pkt_cnt_v := dbg_pkt_cnt_v + TX_MFB_SOF(i);
                end loop;
                    dbg_tx_pkt_cnt <= dbg_tx_pkt_cnt + dbg_pkt_cnt_v;
            end if;
        end if;
    end process;
    --pragma synthesis_on

end architecture;
