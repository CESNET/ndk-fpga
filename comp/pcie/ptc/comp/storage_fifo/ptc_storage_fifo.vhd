-- ptc_storage_fifo.vhd: MVB+MFB completitions storage FIFO
-- Copyright (C) 2018 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all; -- contains definitions for MVB header fields

-- ----------------------------------------------------------------------------
--                             Entity
-- ----------------------------------------------------------------------------

entity PTC_STORAGE_FIFO is
    generic (
        -- ===================
        -- MVB characteristics
        -- ===================

        -- number of MVB items
        MVB_ITEMS       : integer := 4;
        -- number of MVB items
        MVB_ITEM_WIDTH  : integer := 3*4*8;

        -- ===================
        -- MFB characteristics
        -- ===================

        -- number of regions in word
        MFB_REGIONS     : integer := 4;
        -- number of blocks in region
        MFB_REG_SIZE    : integer := 1;
        -- number of items in block
        MFB_BLOCK_SIZE  : integer := 4;
        -- width  of one item (in bits)
        MFB_ITEM_WIDTH  : integer := 32;

        -- ===================
        -- Others
        -- ===================

        -- Number of MVB/MFB words space in main MVB/MFB storage FIFOX
        MAIN_FIFO_ITEMS        : integer := 512;

        -- Number of MFB words space in input MFB shakedown FIFOX Multi
        INPUT_MFB_FIFOXM_ITEMS : integer := 8;

        -- Target device
        -- "VIRTEX6", "7SERIES", "ULTRASCALE"
        DEVICE            : string  := "ULTRASCALE"
    );
    port (
        ---------------------------------------------------------------------------
        -- Common interface
        ---------------------------------------------------------------------------

        CLK              : in  std_logic;
        RESET            : in  std_logic;

        ---------------------------------------------------------------------------
        -- RX PCIe MVB interface
        ---------------------------------------------------------------------------

        RX_MVB_DATA      : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_MVB_VLD       : in  std_logic_vector(MVB_ITEMS               -1 downto 0);
        RX_MVB_SRC_RDY   : in  std_logic;
        RX_MVB_DST_RDY   : out std_logic; -- always '1'

        ---------------------------------------------------------------------------
        -- RX MFB interface
        ---------------------------------------------------------------------------

        RX_MFB_DATA      : in  std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF       : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS   : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY   : in  std_logic;
        RX_MFB_DST_RDY   : out std_logic; -- always '1'

        ---------------------------------------------------------------------------
        -- TX PCIe MVB interface
        ---------------------------------------------------------------------------

        TX_MVB_DATA      : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_VLD       : out std_logic_vector(MVB_ITEMS               -1 downto 0);
        TX_MVB_SRC_RDY   : out std_logic;
        TX_MVB_DST_RDY   : in  std_logic;

        ---------------------------------------------------------------------------
        -- TX MFB interface
        ---------------------------------------------------------------------------

        TX_MFB_DATA      : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_SOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF       : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS   : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY   : out std_logic;
        TX_MFB_DST_RDY   : in  std_logic

    );
end entity;

-- ----------------------------------------------------------------------------
--                             Architecture
-- ----------------------------------------------------------------------------

architecture FULL of PTC_STORAGE_FIFO is

    ---------------------------------------------------------------------------
    -- Constants
    ---------------------------------------------------------------------------

    constant MFB_REG_WIDTH     : integer := MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    constant SOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE));
    constant EOF_POS_WIDTH     : integer := max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE));

    ---------------------------------------------------------------------------

    ---------------------------------------------------------------------------
    -- Signals
    ---------------------------------------------------------------------------

    -- Input MFB compaction (removes empty regions between frames)
    signal compactor_rx_dst_rdy : std_logic;
    signal compactor_tx_data    : std_logic_vector(MFB_REGIONS*MFB_REG_WIDTH-1 downto 0);
    signal compactor_tx_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal compactor_tx_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal compactor_tx_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal compactor_tx_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal compactor_tx_src_rdy : std_logic;
    signal compactor_tx_dst_rdy : std_logic;

    -- Number of MVB items to safely read from storage
    signal mvb_fifo_full       : std_logic;
    signal mvb_fifo_rd         : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_fifo_empty      : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal safe_mvb_items_reg  : unsigned(log2(MAIN_FIFO_ITEMS*MFB_REGIONS+1)-1 downto 0);

    -- Main MFB FIFO input (output of the main MFB storage FIFO)
    signal main_mfb_fifo_in_data    : std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
    signal main_mfb_fifo_in_sof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal main_mfb_fifo_in_eof     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal main_mfb_fifo_in_sof_pos : std_logic_vector(MFB_REGIONS*SOF_POS_WIDTH-1 downto 0);
    signal main_mfb_fifo_in_eof_pos : std_logic_vector(MFB_REGIONS*EOF_POS_WIDTH-1 downto 0);
    signal main_mfb_fifo_in_src_rdy : std_logic;
begin

    -- -------------------------------------------------------------------------
    -- Input MFB compactor
    -- -------------------------------------------------------------------------
    -- Removes empty regions between frames on the write side, so the main MFB
    -- storage FIFO below can be a plain word-granularity FIFO (no per-region
    -- priority read/compaction on the read side, which is what made the old
    -- FIFOX_MULTI-based read path miss timing at 500 MHz/4 regions/1024b).

    input_mfb_compactor_i : entity work.MFB_COMPACTOR
    generic map (
        REGIONS       => MFB_REGIONS,
        REGION_SIZE   => MFB_REG_SIZE,
        BLOCK_SIZE    => MFB_BLOCK_SIZE,
        ITEM_WIDTH    => MFB_ITEM_WIDTH,
        META_WIDTH    => 0,
        FLUSH_TIMEOUT => 8,
        USE_PIPE      => true
    )
    port map (
        CLK   => CLK,
        RESET => RESET,

        RX_DATA    => RX_MFB_DATA,
        RX_SOF_POS => RX_MFB_SOF_POS,
        RX_EOF_POS => RX_MFB_EOF_POS,
        RX_SOF     => RX_MFB_SOF,
        RX_EOF     => RX_MFB_EOF,
        RX_SRC_RDY => RX_MFB_SRC_RDY,
        RX_DST_RDY => compactor_rx_dst_rdy,

        TX_DATA    => compactor_tx_data,
        TX_META    => open,
        TX_SOF_POS => compactor_tx_sof_pos,
        TX_EOF_POS => compactor_tx_eof_pos,
        TX_SOF     => compactor_tx_sof,
        TX_EOF     => compactor_tx_eof,
        TX_SRC_RDY => compactor_tx_src_rdy,
        TX_DST_RDY => compactor_tx_dst_rdy
    );

    RX_MFB_DST_RDY <= compactor_rx_dst_rdy;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Main MFB storage FIFO
    -- -------------------------------------------------------------------------
    -- Plain word-granularity FIFO: the compactor above already delivers dense
    -- (gap-free) words, so no per-region read-side logic is needed here.

    main_mfb_storage_fifo_i : entity work.MFB_FIFOX
    generic map (
        REGIONS             => MFB_REGIONS,
        REGION_SIZE         => MFB_REG_SIZE,
        BLOCK_SIZE          => MFB_BLOCK_SIZE,
        ITEM_WIDTH          => MFB_ITEM_WIDTH,
        META_WIDTH          => 0,
        FIFO_DEPTH          => MAIN_FIFO_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 1
    )
    port map (
        CLK => CLK,
        RST => RESET,

        RX_DATA    => compactor_tx_data,
        RX_SOF_POS => compactor_tx_sof_pos,
        RX_EOF_POS => compactor_tx_eof_pos,
        RX_SOF     => compactor_tx_sof,
        RX_EOF     => compactor_tx_eof,
        RX_SRC_RDY => compactor_tx_src_rdy,
        RX_DST_RDY => compactor_tx_dst_rdy,

        TX_DATA    => main_mfb_fifo_in_data,
        TX_SOF_POS => main_mfb_fifo_in_sof_pos,
        TX_EOF_POS => main_mfb_fifo_in_eof_pos,
        TX_SOF     => main_mfb_fifo_in_sof,
        TX_EOF     => main_mfb_fifo_in_eof,
        TX_SRC_RDY => main_mfb_fifo_in_src_rdy,
        TX_DST_RDY => TX_MFB_DST_RDY,

        FIFO_STATUS => open,
        FIFO_AFULL  => open,
        FIFO_AEMPTY => open
    );

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Safe MVB items register
    -- -------------------------------------------------------------------------

    -- Number of MVB items to safely read from storage
    safe_mvb_items_reg_pr : process (CLK)
        variable increment : unsigned(log2(MFB_REGIONS+1)-1 downto 0);
        variable decrement : unsigned(log2(MVB_ITEMS  +1)-1 downto 0);
    begin
        if (rising_edge(CLK)) then
            -- add 1 for every transaction EOF read from main MFB FIFO
            increment := (others => '0');
            for i in 0 to MFB_REGIONS-1 loop
                if (TX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1' and TX_MFB_EOF(i) = '1') then
                    increment := increment+1;
                end if;
            end loop;

            -- substract 1 for every MVB item read from main MVB FIFO
            decrement := (others => '0');
            for i in 0 to MVB_ITEMS-1 loop
                if (TX_MVB_SRC_RDY = '1' and TX_MVB_DST_RDY = '1' and TX_MVB_VLD(i) = '1') then
                    decrement := decrement+1;
                end if;
            end loop;

            -- set new register value
            safe_mvb_items_reg <= safe_mvb_items_reg + resize(increment,safe_mvb_items_reg'length) - resize(decrement,safe_mvb_items_reg'length);

            if (RESET = '1') then
                safe_mvb_items_reg <= (others => '0');
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- OUTPUT MFB REGISTER
    -- -------------------------------------------------------------------------

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY = '1') then
                TX_MFB_DATA    <= main_mfb_fifo_in_data;
                TX_MFB_SOF_POS <= main_mfb_fifo_in_sof_pos;
                TX_MFB_EOF_POS <= main_mfb_fifo_in_eof_pos;
                TX_MFB_SOF     <= main_mfb_fifo_in_sof;
                TX_MFB_EOF     <= main_mfb_fifo_in_eof;
                TX_MFB_SRC_RDY <= main_mfb_fifo_in_src_rdy;
            end if;
            if (RESET = '1') then
                TX_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -- -------------------------------------------------------------------------

    -- -------------------------------------------------------------------------
    -- Main MVB FIFOX
    -- -------------------------------------------------------------------------

    RX_MVB_DST_RDY <= not mvb_fifo_full;

    mvb_main_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => MVB_ITEM_WIDTH,
        ITEMS               => MVB_ITEMS*MAIN_FIFO_ITEMS,
        WRITE_PORTS         => MVB_ITEMS,
        READ_PORTS          => MVB_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 1,
        ALMOST_EMPTY_OFFSET => 1,
        SAFE_READ_MODE      => true
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,

        DI          => RX_MVB_DATA,
        WR          => RX_MVB_SRC_RDY and RX_MVB_VLD,
        FULL        => mvb_fifo_full,
        AFULL       => open,

        DO          => TX_MVB_DATA,
        RD          => mvb_fifo_rd,
        EMPTY       => mvb_fifo_empty,
        AEMPTY      => open
    );

    -- psl assert_fifo_dst_rdy :
    --      assert always (not (RX_MVB_DST_RDY = '0')) abort (RESET) @rising_edge(CLK)
    --      report "PTC: Storage main MVB FIFO dst_rdy fall error!";

    -- safe MVB items checking
    safe_mvb_items_check_pr : process (safe_mvb_items_reg,TX_MVB_DST_RDY,mvb_fifo_empty)
    begin
        -- read from FIFO, send TX MVB, count number of sent items
        mvb_fifo_rd <= (others => '0');
        TX_MVB_VLD  <= (others => '0');
        for i in 0 to MVB_ITEMS-1 loop
            if (i < safe_mvb_items_reg) then
                mvb_fifo_rd(i) <= TX_MVB_DST_RDY;
                TX_MVB_VLD (i) <= not mvb_fifo_empty(i);
            end if;
        end loop;
    end process;

    TX_MVB_SRC_RDY <= (or TX_MVB_VLD);

    -- -------------------------------------------------------------------------

end architecture;
