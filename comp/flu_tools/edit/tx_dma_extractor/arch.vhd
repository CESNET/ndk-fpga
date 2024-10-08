-- Copyright (C) 2018 CESNET
-- Author(s): Mario Kuka <kuka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture FULL of TX_DMA_EXTRACTOR is
    signal pipe_sel : std_logic;

    signal sze_head : std_logic_vector(63 downto 0);
    subtype hdr_size_range  is natural range 23 downto 16;
    subtype ifc_range       is natural range 39 downto 32;

    signal ifc_fifo_empty   : std_logic;
    signal ifc_fifo_full    : std_logic;
    signal ifc_fifo_wr      : std_logic;
    signal ifc_fifo         : std_logic_vector(7 downto 0);

    signal new_sop_pos      : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
    signal new_sop          : std_logic;
    signal next_sop         : std_logic;

    signal tx_fifo_src_rdy  : std_logic;
    signal tx_fifo_dst_rdy  : std_logic;

begin
   full: if SUPPORT = true generate
        -- remove first 8 bytes from RX data stream
        new_sop_pos <= std_logic_vector(unsigned(RX_SOP_POS) + 1) when next_sop = '0' else
                       (others => '0');

        new_sop     <= '1'      when next_sop = '1' else
                       RX_SOP   when RX_SOP_POS /= (RX_SOP_POS'range => '1') else
                       '0';

        next_sop_pos: process(CLK)
        begin
            if (CLK'event AND CLK = '1') then
                if (RESET = '1') then
                    next_sop <= '0';
                elsif (RX_SRC_RDY and RX_DST_RDY) then
                    next_sop <= '0';
                    if (RX_SOP = '1' and RX_SOP_POS = (RX_SOP_POS'range => '1')) then
                        next_sop <= '1';
                    end if;
                end if;
            end if;
        end process;

        RX_DST_RDY <= tx_fifo_dst_rdy and (not RX_SOP or not ifc_fifo_full);


        -- select sze header from flu word
        mux_fist_word: entity work.GEN_MUX
        generic map (
           DATA_WIDTH  => 64,
           MUX_WIDTH   => 8
        )
        port map (
           DATA_IN     => RX_DATA,
           SEL         => RX_SOP_POS,
           DATA_OUT    => sze_head
        );

        -- get number of interface form sze head
        ifc_fifo <= (others => '0') when sze_head(hdr_size_range) = (hdr_size_range => '0') else
                    sze_head(ifc_range);

        -- TX FIFO
        tx_fifo_src_rdy <= RX_SRC_RDY and (not RX_SOP or not ifc_fifo_full);
        tx_pipe: entity work.FLU_FIFOX
        generic map (
            ITEMS         => TX_FIFO_SIZE,
            DEVICE        => DEVICE,
            DATA_WIDTH    => DATA_WIDTH,
            SOP_POS_WIDTH => SOP_POS_WIDTH
        )
        port map (
            CLK          => CLK,
            RESET        => RESET,
            RX_DATA      => RX_DATA,
            RX_SOP_POS   => new_sop_pos,
            RX_EOP_POS   => RX_EOP_POS,
            RX_SOP       => new_sop,
            RX_EOP       => RX_EOP,
            RX_SRC_RDY   => tx_fifo_src_rdy,
            RX_DST_RDY   => tx_fifo_dst_rdy,
            TX_DATA      => TX_DATA,
            TX_SOP_POS   => TX_SOP_POS,
            TX_EOP_POS   => TX_EOP_POS,
            TX_SOP       => TX_SOP,
            TX_EOP       => TX_EOP,
            TX_SRC_RDY   => TX_SRC_RDY,
            TX_DST_RDY   => TX_DST_RDY
        );

        ifc_fifo_wr <= RX_SRC_RDY and tx_fifo_dst_rdy and RX_SOP;
        -- IFC FIFO
        fifo: entity work.FIFOX
        generic map (
            DATA_WIDTH  => 8,
            ITEMS       => IFC_FIFO_SIZE,
            DEVICE      => DEVICE
        )
        port map(
            CLK         => CLK,
            RESET       => RESET,

            DI          => ifc_fifo,
            WR          => ifc_fifo_wr,
            FULL        => ifc_fifo_full,

            DO          => IFC,
            RD          => IFC_DST_RDY,
            EMPTY       => ifc_fifo_empty
        );
        IFC_SRC_RDY  <= not ifc_fifo_empty;

    end generate;

    empty: if SUPPORT = false generate
        TX_DATA     <= RX_DATA;
        TX_SOP_POS  <= RX_SOP_POS;
        TX_EOP_POS  <= RX_EOP_POS;
        TX_SOP      <= RX_SOP;
        TX_EOP      <= RX_EOP;
        TX_SRC_RDY  <= RX_SRC_RDY;
        RX_DST_RDY  <= TX_DST_RDY;

        IFC         <= (others => '0');
        IFC_SRC_RDY <= '1';
    end generate;
end architecture;
