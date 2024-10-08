-- dma_hdr_extractor.vhd: Extract header from incoming packet form TX dma flu stream.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Mario Kuka <kuka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.math_pack.all;

-- --------------------------------------------------------------
-- Extract header from an incoming packet from TX dma flu stream.
-- --------------------------------------------------------------
entity DMA_HDR_EXTRACTOR is
    generic(
        -- FrameLinkUnaligned Data Width
        DATA_WIDTH    : integer := 512;
        SOP_POS_WIDTH : integer := 3;
        CHANNEL_WIDTH : integer := 8
    );
    port(
        -- Common interface
        CLK         : in  std_logic;
        RESET       : in  std_logic; -- NOTE: also starts debug counters
        -- Input packet form DMA
        RX_CHANNEL  : in  std_logic_vector(CHANNEL_WIDTH-1 downto 0);
        RX_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_SOP_POS  : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
        RX_EOP_POS  : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        RX_SOP      : in  std_logic;
        RX_EOP      : in  std_logic;
        RX_SRC_RDY  : in  std_logic;
        RX_DST_RDY  : out std_logic;
        -- Output truncated packet and extracted header.
        -- Header size is equal to CHANNEL_WIDTH + 8 bytes header
        -- Format: | CHANNEL  | 8 bytes |
        --         N                    0
        TX_HDR      : out std_logic_vector(8*8+CHANNEL_WIDTH-1 downto 0);
        TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_SOP_POS  : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
        TX_EOP_POS  : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        TX_SOP      : out std_logic;
        TX_EOP      : out std_logic;
        TX_SRC_RDY  : out std_logic;
        TX_DST_RDY  : in  std_logic
    );
end entity;

architecture FULL of DMA_HDR_EXTRACTOR is
    signal rx_sop_pos_last : std_logic;
    signal reg_shift_sop   : std_logic;
    signal reg_rx_channel  : std_logic_vector(CHANNEL_WIDTH-1 downto 0);
    signal rx_header       : std_logic_vector(8*8-1 downto 0);
    signal reg_rx_header   : std_logic_vector(8*8-1 downto 0);
begin
    rx_sop_pos_last <= '1' when RX_SOP_POS = (SOP_POS_WIDTH-1 downto 0 => '1') else '0';

    -- Extract header
    mux_i : entity work.GEN_MUX
    generic map (
        DATA_WIDTH => DATA_WIDTH / (2**SOP_POS_WIDTH),
        MUX_WIDTH  => 2**SOP_POS_WIDTH
    )
    port map(
        DATA_IN  => RX_DATA,
        SEL      => RX_SOP_POS,
        DATA_OUT => rx_header
    );

    RX_DST_RDY <= TX_DST_RDY;
    TX_DATA    <= RX_DATA;
    TX_HDR     <= RX_CHANNEL & rx_header when reg_shift_sop = '0' else
                  reg_rx_channel & reg_rx_header;
    TX_EOP     <= RX_EOP;
    TX_EOP_POS <= RX_EOP_POS;
    TX_SOP     <= reg_shift_sop or (RX_SOP and not rx_sop_pos_last);
    TX_SOP_POS <= std_logic_vector(unsigned(RX_SOP_POS) + 1) when reg_shift_sop = '0' else
                  (others => '0');
    TX_SRC_RDY <= RX_SRC_RDY and (not rx_sop_pos_last or not RX_SOP or RX_EOP);

    remove_header_p : process(CLK)
    begin
        if(CLK'event and CLK = '1') then
            if(RESET = '1') then
                reg_shift_sop <= '0';
            elsif(RX_SRC_RDY = '1' and RX_DST_RDY = '1' and RX_SOP = '1' and rx_sop_pos_last = '1') then
                reg_rx_channel <= RX_CHANNEL;
                reg_rx_header  <= rx_header;
                reg_shift_sop  <= '1';
            elsif(RX_SRC_RDY = '1' and RX_DST_RDY = '1') then
                reg_shift_sop  <= '0';
            end if;
        end if;
    end process;
end architecture;
