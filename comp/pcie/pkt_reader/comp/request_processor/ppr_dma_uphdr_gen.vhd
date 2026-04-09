-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;


-- This module prepares DMA headers for the PTC.
--
entity PPR_DMA_UPHDR_GEN is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS       : natural := 1;
        MVB_META_WIDTH  : natural := 0;
        -- Maximum packet size in bytes
        PKT_MTU         : integer := 2**12;
        ADDRESS_WIDTH   : natural := 64;
        DEVICE          : string := "AGILEX"
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_META    : in  std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
        RX_MVB_ADDRESS : in  std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VALID   : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        -- ========================================================
        -- TX Interface
        -- ========================================================

        -- Contains DMA Upstream header
        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
        -- Metadata for internal logic (not sent to PTC)
        TX_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        -- ========================================================
        -- Tag Interface
        -- ========================================================

        -- Receives freed tags for reuse
        FREE_TAG : in  std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
        FREE_VLD : in  std_logic_vector(MVB_ITEMS-1 downto 0)
    );
end entity;

architecture FULL of PPR_DMA_UPHDR_GEN is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    -- Number 4 ("100") resized to two bits.
    constant TWO_ZEROS : unsigned(1 downto 0) := "00";

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal tr_cnt         : unsigned(DMA_REQUEST_TAG_W-1 downto 0);
    signal tr_cnt_full    : std_logic;
    signal init_tags      : std_logic;

    signal tag_fifo_di    : std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
    signal tag_fifo_wr    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tag_fifo_full  : std_logic;
    signal tag_fifo_do    : std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
    signal tag_fifo_rd    : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal tag_fifo_empty : std_logic_vector(MVB_ITEMS-1 downto 0);

    signal length_dwords  : unsigned(log2(PKT_MTU/4+1)-1 downto 0);
    signal dma_uphdr_data : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY and not init_tags and not tag_fifo_empty(0);

    -- =====================================================================
    --  Tag management
    -- =====================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            tr_cnt <= tr_cnt + 1;
            if (RESET = '1') then
                tr_cnt <= (others => '0');
            end if;
        end if;
    end process;

    tr_cnt_full <= and tr_cnt;

    -- Initialization phase: since Reset until all Tags are loaded into the Tag FIFO.
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (tr_cnt_full = '1') then
                init_tags <= '0';
            end if;
            if (RESET = '1') then
                init_tags <= '1';
            end if;
        end if;
    end process;

    -- Load Tags into the Tag FIFO: in the init phase, one per word (no-rush approach)
    process (all)
    begin
        tag_fifo_di <= (others => '0');
        if (init_tags = '1') then
            tag_fifo_di(DMA_REQUEST_TAG_W-1 downto 0) <= std_logic_vector(tr_cnt);
        else
            tag_fifo_di <= FREE_TAG;
        end if;
    end process;

    tag_fifo_wr <= init_tags or FREE_VLD;

    -- psl assert_write_full_fifo :
    --      assert always (tag_fifo_wr = (MVB_ITEMS-1 downto 0 => '0') or tag_fifo_full = '0') abort (RESET) @rising_edge(CLK)
    --      report "PPR_DMA_UPHDR_GEN - tag_fifo_i: trying to Write to a Full FIFO!";

    tag_fifo_i : entity work.FIFOX_MULTI
    generic map (
        DATA_WIDTH          => DMA_REQUEST_TAG_W,
        ITEMS               => 2**DMA_REQUEST_TAG_W, -- enough to store all tags
        WRITE_PORTS         => MVB_ITEMS,
        READ_PORTS          => MVB_ITEMS,
        RAM_TYPE            => "AUTO",
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => 0,
        ALMOST_EMPTY_OFFSET => 0,
        ALLOW_SINGLE_FIFO   => True,
        SAFE_READ_MODE      => True
    )
    port map (
        CLK    => CLK,
        RESET  => RESET,

        DI     => tag_fifo_di,
        WR     => tag_fifo_wr,
        FULL   => tag_fifo_full, -- should never overflow
        AFULL  => open,

        DO     => tag_fifo_do,
        RD     => tag_fifo_rd,
        EMPTY  => tag_fifo_empty,
        AEMPTY => open
    );

    tag_fifo_rd <= (others => RX_MVB_SRC_RDY and TX_MVB_DST_RDY);

    -- =====================================================================
    --  Header creation
    -- =====================================================================

    -- Convert to DWORDS
    length_dwords <= unsigned(RX_MVB_LENGTH(RX_MVB_LENGTH'high downto 2)) + (or RX_MVB_LENGTH(1 downto 0));

    dma_uphdr_data(DMA_REQUEST_LENGTH  ) <= std_logic_vector(resize(length_dwords, DMA_REQUEST_LENGTH_W));
    dma_uphdr_data(DMA_REQUEST_TYPE    ) <= DMA_TYPE_READ;
    -- Packets are aligned to the beginning of the word (hence also beginning of DWORD)
    dma_uphdr_data(DMA_REQUEST_FIRSTIB ) <= (others => '0');
    -- Number of invalid bytes in the last DWORD of the transaction
    dma_uphdr_data(DMA_REQUEST_LASTIB  ) <= std_logic_vector(TWO_ZEROS - unsigned(RX_MVB_LENGTH(1 downto 0)));
    dma_uphdr_data(DMA_REQUEST_TAG     ) <= tag_fifo_do(DMA_REQUEST_TAG_W-1 downto 0);
    dma_uphdr_data(DMA_REQUEST_UNITID  ) <= (others => '0');
    dma_uphdr_data(DMA_REQUEST_GLOBAL  ) <= std_logic_vector(resize(unsigned(RX_MVB_ADDRESS), DMA_REQUEST_GLOBAL_W));
    dma_uphdr_data(DMA_REQUEST_VFID    ) <= (others => '0');
    dma_uphdr_data(DMA_REQUEST_PASID   ) <= (others => '0');
    dma_uphdr_data(DMA_REQUEST_PASIDVLD) <= (others => '0');
    dma_uphdr_data(DMA_REQUEST_RELAXED ) <= (others => '0');

    -- =====================================================================
    --  Output register
    -- =====================================================================

    output_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MVB_DST_RDY = '1') then
                TX_MVB_DATA    <= dma_uphdr_data;
                TX_MVB_META    <= RX_MVB_META;
                TX_MVB_VLD     <= RX_MVB_VALID and not tag_fifo_empty;
                TX_MVB_SRC_RDY <= RX_MVB_SRC_RDY;
            end if;
            if (RESET = '1') then
                TX_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
