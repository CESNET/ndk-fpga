-- metadata_insertor.vhd: Metadata Insertor
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                           Description
-- ----------------------------------------------------------------------------

-- Takes items from input MVB stream and inserts them to MFB stream as metadata
-- without affecting the MFB flow in any other way.
--
entity METADATA_INSERTOR is
generic(
    -- =============================
    -- MVB characteristics
    -- =============================

    MVB_ITEMS       : integer := 2;
    MVB_ITEM_WIDTH  : integer := 128;

    -- =============================
    -- MFB characteristics
    -- =============================

    MFB_REGIONS     : integer := 2;
    MFB_REGION_SIZE : integer := 1;
    MFB_BLOCK_SIZE  : integer := 8;
    MFB_ITEM_WIDTH  : integer := 32;

    -- Width of default MFB metadata
    MFB_META_WIDTH  : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Metadata insertion mode options:
    --   - 0 - Insert in SOF Region
    --   - 1 - Insert in EOF Region
    --   - 2 - Insert for valid all regions of the frame. Leads to a slight increase of logic paths. When two frames are present in one region, Metadata will be inserted for the one with SOP.
    INSERT_MODE     : integer := 0;

    -- Input MVB FIFO size.
    -- Set to 0 for no FIFO at all
    MVB_FIFO_SIZE   : natural := 0;

    -- Enable FIFOX Multi for better effectivity
    -- MVB_FIFO_SIZE must be >= 16
    MVB_FIFOX_MULTI : boolean := False;

    -- Target device:
    --   - "ULTRASCALE",
    --   - "7SERIES"
    DEVICE          : string  := "ULTRASCALE"
);
port(
    -- =============================
    -- Clock and Reset
    -- =============================

    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- =============================
    -- RX MVB
    -- =============================

    RX_MVB_DATA     : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    RX_MVB_VLD      : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
    RX_MVB_SRC_RDY  : in  std_logic;
    RX_MVB_DST_RDY  : out std_logic;

    -- =============================
    -- RX MFB
    -- =============================

    RX_MFB_DATA     : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Gets propagated to TX MFB without change
    RX_MFB_META     : in  std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => '0');
    RX_MFB_SOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_EOF      : in  std_logic_vector(MFB_REGIONS-1 downto 0);
    RX_MFB_SOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    RX_MFB_EOF_POS  : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    RX_MFB_SRC_RDY  : in  std_logic;
    RX_MFB_DST_RDY  : out std_logic;

    -- =============================
    -- TX MFB
    -- =============================

    TX_MFB_DATA     : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    -- Original Metadata from RX MFB
    TX_MFB_META     : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
    -- Inserted metadata from RX MVB
    TX_MFB_META_NEW : out std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    TX_MFB_SOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_EOF      : out std_logic_vector(MFB_REGIONS-1 downto 0);
    TX_MFB_SOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
    TX_MFB_EOF_POS  : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
    TX_MFB_SRC_RDY  : out std_logic;
    TX_MFB_DST_RDY  : in  std_logic

);
end entity;

architecture FULL of METADATA_INSERTOR is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    signal fifo_mvb_data     : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
    signal fifo_mvb_vld      : std_logic_vector(MVB_ITEMS               -1 downto 0);
    signal fifo_mvb_src_rdy  : std_logic;
    signal fifo_mvb_dst_rdy  : std_logic;

    signal fifox_wr          : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal fifox_full        : std_logic;

    signal shake_tx_data     : std_logic_vector(MFB_REGIONS*MVB_ITEM_WIDTH-1 downto 0);
    signal shake_tx_data_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(MVB_ITEM_WIDTH-1 downto 0);
    signal shake_tx_vld_n    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shake_tx_vld      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal shake_tx_next     : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal RX_MFB_XOF         : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal rx_mfb_xof_present : std_logic;
    signal rx_mfb_xof_cnt     : u_array_t(MFB_REGIONS+1-1 downto 0)(log2(MFB_REGIONS)-1 downto 0);
    signal rx_mfb_last_hdr_i  : unsigned(log2(MFB_REGIONS)-1 downto 0);
    signal hdrs_rdy           : std_logic;

    ---------------------------------------------------------------------------

begin

    mvb_fifo_g: if not MVB_FIFOX_MULTI generate
        -- ---------------------------------------------------------------------
        -- MVB FIFOX + MVB Shakedown
        -- ---------------------------------------------------------------------

        mvb_fifox_i : entity work.MVB_FIFOX
        generic map(
            ITEMS               => MVB_ITEMS           ,
            ITEM_WIDTH          => MVB_ITEM_WIDTH      ,
            FIFO_DEPTH          => max(MVB_FIFO_SIZE,2),
            RAM_TYPE            => "AUTO"              ,
            DEVICE              => DEVICE              ,
            ALMOST_FULL_OFFSET  => 1                   ,
            ALMOST_EMPTY_OFFSET => 1                   ,
            FAKE_FIFO           => (MVB_FIFO_SIZE=0)
        )
        port map(
            CLK        => CLK  ,
            RESET      => RESET,

            RX_DATA    => RX_MVB_DATA   ,
            RX_VLD     => RX_MVB_VLD    ,
            RX_SRC_RDY => RX_MVB_SRC_RDY,
            RX_DST_RDY => RX_MVB_DST_RDY,

            TX_DATA    => fifo_mvb_data   ,
            TX_VLD     => fifo_mvb_vld    ,
            TX_SRC_RDY => fifo_mvb_src_rdy,
            TX_DST_RDY => fifo_mvb_dst_rdy,

            STATUS     => open,
            AFULL      => open,
            AEMPTY     => open
        );

        mvb_shake_i : entity work.MVB_SHAKEDOWN
        generic map(
            RX_ITEMS    => MVB_ITEMS     ,
            TX_ITEMS    => MFB_REGIONS   ,
            ITEM_WIDTH  => MVB_ITEM_WIDTH,
            SHAKE_PORTS => 2
        )
        port map(
            CLK        => CLK  ,
            RESET      => RESET,

            RX_DATA    => fifo_mvb_data   ,
            RX_VLD     => fifo_mvb_vld    ,
            RX_SRC_RDY => fifo_mvb_src_rdy,
            RX_DST_RDY => fifo_mvb_dst_rdy,

            TX_DATA    => shake_tx_data,
            TX_VLD     => shake_tx_vld ,
            TX_NEXT    => shake_tx_next
        );
        -- ---------------------------------------------------------------------
    else generate
        -- ---------------------------------------------------------------------
        -- MVB FIFOX Multi
        -- ---------------------------------------------------------------------

        fifox_wr <= RX_MVB_SRC_RDY and RX_MVB_VLD;
        RX_MVB_DST_RDY <= not fifox_full;

        mvb_shake_i : entity work.FIFOX_MULTI
        generic map(
            DATA_WIDTH          => MVB_ITEM_WIDTH,
            ITEMS               => max(MVB_ITEMS, MFB_REGIONS)*MVB_FIFO_SIZE,
            WRITE_PORTS         => MVB_ITEMS,
            READ_PORTS          => MFB_REGIONS,
            RAM_TYPE            => "AUTO",
            DEVICE              => DEVICE,
            SAFE_READ_MODE      => false,
            ALMOST_FULL_OFFSET  => 1,
            ALMOST_EMPTY_OFFSET => 1
        )
        port map(
            CLK    => CLK,
            RESET  => RESET,

            DI     => RX_MVB_DATA,
            WR     => fifox_wr,
            FULL   => fifox_full,
            AFULL  => open,

            DO     => shake_tx_data,
            RD     => shake_tx_next,
            EMPTY  => shake_tx_vld_n,
            AEMPTY => open
        );

        shake_tx_vld <= not shake_tx_vld_n;

        -- ---------------------------------------------------------------------
    end generate;

    shake_tx_data_arr  <= slv_array_deser(shake_tx_data, MFB_REGIONS);

    -- -------------------------------------------------------------------------
    -- RX MFB processing
    -- -------------------------------------------------------------------------

    RX_MFB_XOF         <= RX_MFB_EOF when INSERT_MODE=1 else RX_MFB_SOF;
    rx_mfb_xof_present <= (or RX_MFB_XOF) and RX_MFB_SRC_RDY;

    rx_mfb_xof_cnt_pr : process (RX_MFB_XOF)
        variable cnt : integer;
    begin
        rx_mfb_xof_cnt <= (others => (others => '0'));

        -- XOFs count prefix scan
        cnt := 0;
        for i in 0 to MFB_REGIONS-1 loop
            rx_mfb_xof_cnt(i) <= to_unsigned(cnt,log2(MFB_REGIONS));

            if (RX_MFB_XOF(i)='1') then
                cnt := cnt+1;
            end if;
        end loop;
        rx_mfb_xof_cnt(MFB_REGIONS) <= to_unsigned(cnt,log2(MFB_REGIONS));
    end process;

    rx_mfb_last_hdr_i <= rx_mfb_xof_cnt(MFB_REGIONS)-1;
    hdrs_rdy <= '1' when rx_mfb_xof_present='0' or shake_tx_vld(to_integer(rx_mfb_last_hdr_i))='1' else '0';

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- TX MFB Generation
    -- -------------------------------------------------------------------------

    tx_mfb_reg : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_MFB_DST_RDY='1' or TX_MFB_SRC_RDY='0') then
                TX_MFB_DATA    <= RX_MFB_DATA;
                TX_MFB_META    <= RX_MFB_META;
                TX_MFB_SOF     <= RX_MFB_SOF;
                TX_MFB_EOF     <= RX_MFB_EOF;
                TX_MFB_SOF_POS <= RX_MFB_SOF_POS;
                TX_MFB_EOF_POS <= RX_MFB_EOF_POS;
                TX_MFB_SRC_RDY <= RX_MFB_SRC_RDY and hdrs_rdy;

                if (rx_mfb_xof_present='1' or INSERT_MODE/=2) then
                    -- Distribute MVB Items to XOF positions
                    for i in 0 to MFB_REGIONS-1 loop
                        TX_MFB_META_NEW((i+1)*MVB_ITEM_WIDTH-1 downto i*MVB_ITEM_WIDTH) <= shake_tx_data_arr(to_integer(rx_mfb_xof_cnt(i)));
                    end loop;
                end if;
            end if;

            if (RESET='1') then
                TX_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- DST RDY propagation
    -- -------------------------------------------------------------------------

    RX_MFB_DST_RDY <= '1' when (TX_MFB_DST_RDY='1' or TX_MFB_SRC_RDY='0') and hdrs_rdy='1' else '0';

    shake_tx_next_pr : process (all)
    begin
        shake_tx_next <= (others => '0');

        for i in 0 to MFB_REGIONS-1 loop
            if (i<=rx_mfb_last_hdr_i or MFB_REGIONS<2) then
                shake_tx_next(i) <= '1' when (TX_MFB_DST_RDY='1' or TX_MFB_SRC_RDY='0') and rx_mfb_xof_present='1' and shake_tx_vld(to_integer(rx_mfb_last_hdr_i))='1' else '0';
            end if;
        end loop;
    end process;

    -- -------------------------------------------------------------------------

end architecture;
