-- Copyright (C) 2025 CESNET z. s. p. o.
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
entity PPW_DMA_UPHDR_GEN is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS       : natural := 1;
        -- Maximum packet size in bytes
        PKT_MTU         : integer := 2**12;
        ADDRESS_WIDTH   : natural := 64
    );
    port (
        CLK   : in std_logic;
        RESET : in std_logic;

        -- ========================================================
        -- RX Interface
        -- ========================================================

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
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PPW_DMA_UPHDR_GEN is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    -- Number 4 ("100") resized to two bits.
    constant TWO_ZEROS : unsigned(1 downto 0) := "00";

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal tr_cnt             : unsigned(DMA_REQUEST_TAG_W-1 downto 0);
    signal length_bytes_total : unsigned(log2(PKT_MTU+1)+1-1 downto 0);
    signal length_dwords      : unsigned(log2(PKT_MTU/4+1)+1-1 downto 0);
    signal dma_uphdr_data     : std_logic_vector(DMA_UPHDR_WIDTH-1 downto 0);

begin

    RX_MVB_DST_RDY <= TX_MVB_DST_RDY;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((RX_MVB_SRC_RDY = '1') and (TX_MVB_DST_RDY = '1')) then
                tr_cnt <= tr_cnt + to_unsigned(count_ones(RX_MVB_VALID), DMA_REQUEST_TAG_W);
            end if;
            if (RESET = '1') then
                tr_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- Convert to DWORDS
    -- 1. Total bytes is length + byte offset (lower 2 bits of address)
    length_bytes_total <= resize(unsigned(RX_MVB_LENGTH), length_bytes_total'length) + unsigned(RX_MVB_ADDRESS(1 downto 0));
    -- 2. Round up to dwords
    length_dwords      <= length_bytes_total(length_bytes_total'high downto 2) + (or length_bytes_total(1 downto 0));

    dma_uphdr_data(DMA_REQUEST_LENGTH  ) <= std_logic_vector(resize(length_dwords, DMA_REQUEST_LENGTH_W));
    dma_uphdr_data(DMA_REQUEST_TYPE    ) <= DMA_TYPE_WRITE;
    -- Compensates for the dword-aligned address by identifying the number of invalid bytes from the start.
    dma_uphdr_data(DMA_REQUEST_FIRSTIB ) <= RX_MVB_ADDRESS(1 downto 0);
    -- Number of invalid bytes in the last DWORD of the transaction.
    dma_uphdr_data(DMA_REQUEST_LASTIB  ) <= std_logic_vector(TWO_ZEROS - unsigned(length_bytes_total(1 downto 0)));
    dma_uphdr_data(DMA_REQUEST_TAG     ) <= std_logic_vector(tr_cnt);
    dma_uphdr_data(DMA_REQUEST_UNITID  ) <= (others => '0');
    -- Word-aligning the address (dword is 4 bytes -> drive two LSBs low).
    dma_uphdr_data(DMA_REQUEST_GLOBAL  ) <= RX_MVB_ADDRESS(DMA_REQUEST_GLOBAL_W-1 downto 2) & "00";
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
                TX_MVB_VLD     <= RX_MVB_VALID;
                TX_MVB_SRC_RDY <= RX_MVB_SRC_RDY;
            end if;
            if (RESET = '1') then
                TX_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
