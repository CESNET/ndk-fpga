-- checksum_calculator.vhd: A top-level component that can calculate checksums using the IPv4=TCP=UDP checksum algorithm.
-- Copyright (C) 2022 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- ============================================================================
--  Description
-- ============================================================================

-- This component calculates checksum from the Section of each frame specified by the Offset and Length.
-- The IPv4(=TCP=UDP) checksum algorithm is used.
-- The calculation can be "disabled" per each frame by setting the RX_CHSUM_EN to 0.
-- This dis/enabling of the checksum results in propagating the inverted value of the RX_CHSUM_EN to the TX_CHSUM_BYPASS output (to be reworked).
entity CHECKSUM_CALCULATOR is
generic(
    -- Number of Regions within a data word, must be power of 2.
    MFB_REGIONS     : natural := 4;
    -- Region size (in Blocks).
    MFB_REGION_SIZE : natural := 8;
    -- Block size (in Items).
    MFB_BLOCK_SIZE  : natural := 8;
    -- Item width (in bits), must be 8.
    MFB_ITEM_WIDTH  : natural := 8;
    -- Metadata width (in bits), valid with SOF.
    MFB_META_WIDTH  : natural := 0;

    -- Maximum size of a packet (in Items).
    PKT_MTU         : natural := 2**14;

    -- Width of each Offset signal in the in the RX_OFFSET vector.
    OFFSET_WIDTH    : integer := 7;
    -- Width of each Length signal in the in the RX_LENGTH vector.
    LENGTH_WIDTH    : integer := 9;

    -- Select Network order (checksum bytes are swapped at the output).
    NETWORK_ORDER   : boolean := False;
    -- FPGA device name.
    -- Options: ULTRASCALE, STRATIX10, AGILEX, ...
    DEVICE          : string := "STRATIX10"
);
port(
    -- ========================================================================
    -- Clock and Reset
    -- ========================================================================

    CLK   : in  std_logic;
    RESET : in  std_logic;

    -- ========================================================================
    -- RX STREAM
    --
    -- #. Input packets (MFB),
    -- #. Meta information (header offsets and lengths).
    -- ========================================================================

    RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    RX_MFB_META    : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SRC_RDY : in  std_logic;
    RX_MFB_DST_RDY : out std_logic;

    -- Header offset from SOF POS, valid with SOF.
    RX_OFFSET      : in  std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);
    -- Header length, valid with SOF.
    RX_LENGTH      : in  std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
    -- Enable checksum calculation, valid with SOF.
    RX_CHSUM_EN    : in  std_logic_vector(MFB_REGIONS-1 downto 0);

    -- ========================================================================
    -- TX MVB STREAM
    --
    -- Calculated checksums.
    -- ========================================================================

    -- The calculated checksum.
    TX_MVB_DATA     : out std_logic_vector(MFB_REGIONS*16-1 downto 0);
    TX_MVB_META     : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    -- Bypass checksum insertion (=> checksum caluculation is not desired).
    TX_CHSUM_BYPASS : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MVB_VLD      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MVB_SRC_RDY  : out std_logic := '0';
    TX_MVB_DST_RDY  : in  std_logic := '1'
);
end entity;

architecture FULL of CHECKSUM_CALCULATOR is

    -- ========================================================================
    --                                CONSTANTS
    -- ========================================================================

    constant CHECKSUM_W       : natural := 16;

    constant MFB_DATA_W       : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_DATA_ITEMS   : natural := MFB_DATA_W/MFB_ITEM_WIDTH;
    constant MFB_REGION_ITEMS : natural := MFB_DATA_ITEMS/MFB_REGIONS;

    -- "serial", "parallel", "prefixsum"
    constant AGGREGATE_IMPL   : string := "prefixsum";

    -- ========================================================================
    --                                FUNCTIONS
    -- ========================================================================

    function int_is_odd(int : integer) return std_logic is
        variable slv : std_logic_vector(32-1 downto 0);
        variable odd : std_logic;
    begin
        slv := std_logic_vector(to_unsigned(int, 32));
        odd := slv(0);
        return odd;
    end;

    -- ========================================================================
    --                                 SIGNALS
    -- ========================================================================

    -- Metadata FIFOXM signals
    signal rx_mfb_meta_arr      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH   -1 downto 0);
    signal meta_fifoxm_din_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH+1 -1 downto 0);
    signal meta_fifoxm_din      : std_logic_vector(MFB_REGIONS*           (MFB_META_WIDTH+1)-1 downto 0);
    signal meta_fifoxm_wr       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal meta_fifoxm_full     : std_logic;
    signal meta_fifoxm_dout     : std_logic_vector(MFB_REGIONS*           (MFB_META_WIDTH+1)-1 downto 0);
    signal meta_fifoxm_dout_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH+1 -1 downto 0);
    signal meta_fifoxm_rd       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal meta_fifoxm_empty    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal meta_fifoxm_out_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal meta_fifoxm_vo       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal meta_fifoxm_meta_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_META_WIDTH-1 downto 0);
    signal meta_fifoxm_bypass   : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- input register
    signal rx_ext_data           : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal rx_ext_sof_pos        : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    signal rx_ext_eof_pos        : std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    signal rx_ext_sof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_ext_eof            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_ext_src_rdy        : std_logic;
    signal rx_ext_dst_rdy        : std_logic;
    signal rx_ext_off            : std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);
    signal rx_ext_len            : std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
    signal rx_ext_en             : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- validated (extracted) checksum data signals
    signal tx_ext_data        : std_logic_vector(MFB_DATA_W-1 downto 0);
    signal tx_ext_odd         : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);
    -- signal tx_ext_odd_reg     : std_logic;
    signal tx_ext_vld         : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);
    signal tx_ext_end         : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);
    signal tx_ext_src_rdy     : std_logic;
    signal tx_ext_dst_rdy     : std_logic;

    signal tx_ext_end_reg     : std_logic;
    signal odd_start          : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);
    signal last_vld_din       : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);
    signal last_vld_vld       : std_logic_vector(MFB_DATA_ITEMS-1 downto 0);

    -- regional checksum signals
    signal rx_rchsum_data     : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_DATA_W/MFB_REGIONS-1 downto 0);
    signal rx_rchsum_odd      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_ITEMS-1 downto 0);
    signal rx_rchsum_end      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_ITEMS-1 downto 0);
    signal rx_rchsum_vld      : slv_array_t     (MFB_REGIONS-1 downto 0)(MFB_REGION_ITEMS-1 downto 0);
    signal rx_rchsum_src_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_rchsum_dst_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal tx_rchsum_data     : slv_array_t     (MFB_REGIONS-1 downto 0)(2*CHECKSUM_W-1 downto 0);
    signal tx_rchsum_end      : slv_array_t     (MFB_REGIONS-1 downto 0)(2-1 downto 0);
    signal tx_rchsum_vld      : slv_array_t     (MFB_REGIONS-1 downto 0)(2-1 downto 0);
    signal tx_rchsum_src_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal tx_rchsum_dst_rdy  : std_logic_vector(MFB_REGIONS-1 downto 0);

    -- finalized checksum signals
    signal rx_fchsum_data     : std_logic_vector(MFB_REGIONS*2*CHECKSUM_W-1 downto 0);
    signal rx_fchsum_end      : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal rx_fchsum_vld      : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal rx_fchsum_src_rdy  : std_logic;
    signal rx_fchsum_dst_rdy  : std_logic;

    signal tx_fchsum_data     : std_logic_vector(MFB_REGIONS*2*CHECKSUM_W-1 downto 0);
    signal tx_fchsum_vld      : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal tx_fchsum_src_rdy  : std_logic;
    signal tx_fchsum_dst_rdy  : std_logic;

    -- checksum FIFOX Multi and output signals
    signal fifoxm_datain      : std_logic_vector(MFB_REGIONS*2*CHECKSUM_W-1 downto 0);
    signal fifoxm_wr          : std_logic_vector(MFB_REGIONS*2-1 downto 0);
    signal fifoxm_full        : std_logic;

    signal fifoxm_dataout     : std_logic_vector(MFB_REGIONS*CHECKSUM_W-1 downto 0);
    signal fifoxm_rd          : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifoxm_empty       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifoxm_out_rdy     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal fifoxm_vo          : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal tx_mvb_data_reordered : std_logic_vector(MFB_REGIONS*CHECKSUM_W-1 downto 0);

begin

    assert MFB_ITEM_WIDTH=8
        report "CHECKSUM CALCULATOR: MFB_ITEM_WIDTH must be 8!" &
               "MFB_ITEM_WIDTH is currently " & integer'image(MFB_ITEM_WIDTH)
        severity Failure;

    RX_MFB_DST_RDY <= rx_ext_dst_rdy and not meta_fifoxm_full;

    -- ========================================================================
    --  Checksum enable flags synchronization
    -- ========================================================================

    rx_mfb_meta_arr <= slv_array_deser(RX_MFB_META, MFB_REGIONS);
    rx_meta_g : for r in 0 to MFB_REGIONS-1 generate
        meta_fifoxm_din_arr(r) <= rx_mfb_meta_arr(r) & RX_CHSUM_EN(r);
    end generate;
    meta_fifoxm_din <= slv_array_ser(meta_fifoxm_din_arr);
    meta_fifoxm_wr  <= (RX_MFB_SOF and RX_MFB_SRC_RDY) and RX_MFB_DST_RDY;

    meta_fifoxm_i : entity work.FIFOX_MULTI(shakedown)
    generic map(
        DATA_WIDTH          => MFB_META_WIDTH+1,
        ITEMS               => 512             ,
        WRITE_PORTS         => MFB_REGIONS     ,
        READ_PORTS          => MFB_REGIONS     ,
        RAM_TYPE            => "AUTO"          ,
        DEVICE              => DEVICE          ,
        ALMOST_FULL_OFFSET  => 0               ,
        ALMOST_EMPTY_OFFSET => 0               ,
        ALLOW_SINGLE_FIFO   => True            ,
        SAFE_READ_MODE      => False
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        DI    => meta_fifoxm_din   ,
        WR    => meta_fifoxm_wr    ,
        FULL  => meta_fifoxm_full  ,
        AFULL => open              ,

        DO     => meta_fifoxm_dout ,
        RD     => meta_fifoxm_rd   ,
        EMPTY  => meta_fifoxm_empty,
        AEMPTY => open
    );

    -- valid out
    meta_fifoxm_vo <= not meta_fifoxm_empty;
    meta_fifoxm_read_g : for r in 0 to MFB_REGIONS-1 generate
        meta_fifoxm_out_rdy(r) <= and meta_fifoxm_vo(r downto 0);
        meta_fifoxm_rd     (r) <= meta_fifoxm_out_rdy(r) and fifoxm_out_rdy(r) and TX_MVB_DST_RDY;
    end generate;

    meta_fifoxm_dout_arr <= slv_array_deser(meta_fifoxm_dout, MFB_REGIONS);
    tx_meta_g : for r in 0 to MFB_REGIONS-1 generate
        meta_fifoxm_meta_arr(r) <=     meta_fifoxm_dout_arr(r)(MFB_META_WIDTH+1-1 downto 1);
        meta_fifoxm_bypass  (r) <= not meta_fifoxm_dout_arr(r)(0);
    end generate;

    -- ========================================================================
    --  Input register
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (rx_ext_dst_rdy = '1') then
                rx_ext_data    <= RX_MFB_DATA;
                rx_ext_sof_pos <= RX_MFB_SOF_POS;
                rx_ext_eof_pos <= RX_MFB_EOF_POS;
                rx_ext_sof     <= RX_MFB_SOF;
                rx_ext_eof     <= RX_MFB_EOF;
                rx_ext_src_rdy <= RX_MFB_SRC_RDY and not meta_fifoxm_full;

                rx_ext_off     <= RX_OFFSET;
                rx_ext_len     <= RX_LENGTH;
                rx_ext_en      <= RX_CHSUM_EN;
            end if;

            if (RESET = '1') then
                rx_ext_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    --  Checksum data validation
    -- ========================================================================

    mfb_items_vld_i : entity work.MFB_ITEMS_VLD
    generic map(
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        PKT_MTU         => PKT_MTU        ,
        OFFSET_WIDTH    => OFFSET_WIDTH   ,
        LENGTH_WIDTH    => LENGTH_WIDTH
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_MFB_DATA    => rx_ext_data   ,
        RX_MFB_SOF_POS => rx_ext_sof_pos,
        RX_MFB_EOF_POS => rx_ext_eof_pos,
        RX_MFB_SOF     => rx_ext_sof    ,
        RX_MFB_EOF     => rx_ext_eof    ,
        RX_MFB_SRC_RDY => rx_ext_src_rdy,
        RX_MFB_DST_RDY => rx_ext_dst_rdy,

        RX_OFFSET      => rx_ext_off    ,
        RX_LENGTH      => rx_ext_len    ,
        RX_ENABLE      => (others => '1'),

        TX_DATA        => tx_ext_data   ,
        TX_END         => tx_ext_end    ,
        TX_VLD         => tx_ext_vld    ,
        TX_SRC_RDY     => tx_ext_src_rdy,
        TX_DST_RDY     => tx_ext_dst_rdy
    );


    process(CLK)
    begin
        if rising_edge(CLK) then
            if (tx_ext_src_rdy = '1') and (tx_ext_dst_rdy = '1') then
                tx_ext_end_reg <= tx_ext_end(MFB_DATA_ITEMS-1);
            end if;
            if (RESET = '1') then
                tx_ext_end_reg <= '0';
            end if;
        end if;
    end process;

    odd_start(0) <= '0'; -- not needed tho
    last_vld_din(0) <= '0';
    last_vld_vld(0) <= tx_ext_end_reg;
    odd_sig_g : for i in 1 to MFB_DATA_ITEMS-1 generate
        odd_start   (i) <= not tx_ext_vld(i-1) and tx_ext_vld(i) and int_is_odd(i); -- automatically '0' for all even "i"s
        last_vld_din(i) <= '0' when tx_ext_end(i-1) = '1' else odd_start(i); -- End always overwrites the Odd signal to '0'
        last_vld_vld(i) <= odd_start(i) or tx_ext_end(i-1);
    end generate;

    last_vld_i : entity work.MVB_AGGREGATE_LAST_VLD
    generic map(
        ITEMS          => MFB_DATA_ITEMS,
        ITEM_WIDTH     => 1             ,
        IMPLEMENTATION => AGGREGATE_IMPL,
        INTERNAL_REG   => true          ,
        RESET_DATA     => true
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => last_vld_din  ,
        RX_VLD     => last_vld_vld  ,
        RX_SRC_RDY => tx_ext_src_rdy,
        RX_DST_RDY => tx_ext_dst_rdy,

        REG_IN_DATA  => (others => '0'),
        REG_IN_VLD   => '0',
        REG_OUT_DATA => open,
        REG_OUT_VLD  => open,
        REG_OUT_WR   => open,

        TX_DATA         => tx_ext_odd,
        TX_VLD          => open,
        TX_PRESCAN_DATA => open,
        TX_PRESCAN_VLD  => open,
        TX_SRC_RDY      => open,
        TX_DST_RDY      => (and rx_rchsum_dst_rdy)
    );

    -- ========================================================================
    --  Checksum calculation
    -- ========================================================================

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (and rx_rchsum_dst_rdy) then
                rx_rchsum_data    <= slv_array_deser(tx_ext_data, MFB_REGIONS);
                rx_rchsum_odd     <= slv_array_deser(tx_ext_odd , MFB_REGIONS);
                rx_rchsum_end     <= slv_array_deser(tx_ext_end , MFB_REGIONS);
                rx_rchsum_vld     <= slv_array_deser(tx_ext_vld , MFB_REGIONS);
                rx_rchsum_src_rdy <= (others => tx_ext_src_rdy);
            end if;
            if (RESET = '1') then
                rx_rchsum_vld     <= (others => (others => '0'));
                rx_rchsum_src_rdy <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------
    --  Per-region calculations
    -- -------------------------

    chsum_regional_g : for r in 0 to MFB_REGIONS-1 generate

        chsum_regional_i : entity work.CHSUM_REGIONAL
        generic map(
            ITEMS          => MFB_REGION_ITEMS,
            ITEM_WIDTH     => MFB_ITEM_WIDTH  ,
            CHECKSUM_WIDTH => CHECKSUM_W
        )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_CHSUM_DATA   => rx_rchsum_data   (r),
            RX_CHSUM_ODD    => rx_rchsum_odd    (r),
            RX_CHSUM_END    => rx_rchsum_end    (r),
            RX_VALID        => rx_rchsum_vld    (r),
            RX_SRC_RDY      => rx_rchsum_src_rdy(r),
            RX_DST_RDY      => rx_rchsum_dst_rdy(r),

            TX_CHSUM_REGION => tx_rchsum_data   (r),
            TX_CHSUM_END    => tx_rchsum_end    (r),
            TX_CHSUM_VLD    => tx_rchsum_vld    (r),
            TX_SRC_RDY      => tx_rchsum_src_rdy(r),
            TX_DST_RDY      => tx_rchsum_dst_rdy(r)
        );

    end generate;

    tx_rchsum_dst_rdy <= (others => rx_fchsum_dst_rdy);

    -- -----------------------------------
    --  Checksum calculation finalization
    -- -----------------------------------

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (rx_fchsum_dst_rdy = '1') then
                rx_fchsum_data    <= slv_array_ser(tx_rchsum_data);
                rx_fchsum_end     <= slv_array_ser(tx_rchsum_end );
                rx_fchsum_vld     <= slv_array_ser(tx_rchsum_vld );
                rx_fchsum_src_rdy <= or tx_rchsum_src_rdy;
            end if;
            if (RESET = '1') then
                rx_fchsum_vld     <= (others => '0');
                rx_fchsum_src_rdy <= '0';
            end if;
        end if;
    end process;

    chsum_finalizer_i : entity work.CHSUM_FINALIZER
    generic map(
        REGIONS        => MFB_REGIONS,
        CHECKSUM_WIDTH => CHECKSUM_W
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        RX_CHSUM_REGION => rx_fchsum_data   ,
        RX_CHSUM_END    => rx_fchsum_end    ,
        RX_CHSUM_VLD    => rx_fchsum_vld    ,
        RX_SRC_RDY      => rx_fchsum_src_rdy,
        RX_DST_RDY      => rx_fchsum_dst_rdy,

        TX_CHECKSUM     => tx_fchsum_data   ,
        TX_VALID        => tx_fchsum_vld    ,
        TX_SRC_RDY      => tx_fchsum_src_rdy,
        TX_DST_RDY      => tx_fchsum_dst_rdy
    );

    -- --------------------------------
    -- Output FIFOX MULTI (shakedown)
    -- --------------------------------

    fifoxm_datain <= tx_fchsum_data;
    fifoxm_wr     <= tx_fchsum_vld and not fifoxm_full;
    tx_fchsum_dst_rdy <= not fifoxm_full;

    fifoxm_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => CHECKSUM_W   ,
        ITEMS               => 512          ,
        WRITE_PORTS         => MFB_REGIONS*2,
        READ_PORTS          => MFB_REGIONS  ,
        RAM_TYPE            => "AUTO"       ,
        DEVICE              => DEVICE       ,
        ALMOST_FULL_OFFSET  => 0            ,
        ALMOST_EMPTY_OFFSET => 0            ,
        ALLOW_SINGLE_FIFO   => True         ,
        SAFE_READ_MODE      => False
    )
    port map(
        CLK   => CLK,
        RESET => RESET,

        DI     => fifoxm_datain ,
        WR     => fifoxm_wr     ,
        FULL   => fifoxm_full   ,
        AFULL  => open          ,

        DO     => fifoxm_dataout,
        RD     => fifoxm_rd     ,
        EMPTY  => fifoxm_empty  ,
        AEMPTY => open
    );

    -- valid out
    fifoxm_vo <= not fifoxm_empty;
    fifoxm_dout_g : for r in 0 to MFB_REGIONS-1 generate
        fifoxm_out_rdy(r) <= and fifoxm_vo(r downto 0);
        fifoxm_rd(r) <= meta_fifoxm_out_rdy(r) and fifoxm_out_rdy(r) and TX_MVB_DST_RDY;
    end generate;

    -- ========================================================================
    --  Output assignment
    -- ========================================================================

    byte_order_g : if NETWORK_ORDER generate

        signal tx_mvb_data_reordered_arr : slv_array_t(MFB_REGIONS-1 downto 0)(CHECKSUM_W-1 downto 0);
        signal fifoxm_dataout_arr        : slv_array_t(MFB_REGIONS-1 downto 0)(CHECKSUM_W-1 downto 0);

    begin

        fifoxm_dataout_arr <= slv_array_deser(fifoxm_dataout, MFB_REGIONS);
        -- Byte switcharoo to the Network order
        output_g : for r in 0 to MFB_REGIONS-1 generate
            tx_mvb_data_reordered_arr(r)(CHECKSUM_W  -1 downto CHECKSUM_W/2) <= fifoxm_dataout_arr(r)(CHECKSUM_W/2-1 downto            0);
            tx_mvb_data_reordered_arr(r)(CHECKSUM_W/2-1 downto            0) <= fifoxm_dataout_arr(r)(CHECKSUM_W  -1 downto CHECKSUM_W/2);
        end generate;
        tx_mvb_data_reordered <= slv_array_ser(tx_mvb_data_reordered_arr);

    else generate

        tx_mvb_data_reordered <= fifoxm_dataout;

    end generate;

    TX_MVB_DATA     <= tx_mvb_data_reordered;
    TX_MVB_META     <= slv_array_ser(meta_fifoxm_meta_arr);
    TX_CHSUM_BYPASS <= meta_fifoxm_bypass; -- inverted checksum enable
    TX_MVB_VLD      <= fifoxm_vo and meta_fifoxm_vo;
    TX_MVB_SRC_RDY  <= or TX_MVB_VLD;

end architecture;
