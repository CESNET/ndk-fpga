-- tx_path_40G.vhd : 40G PCS - TX module top level
-- Copyright (C) 2010-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity tx_path_40g is
    generic (
        DEVICE      : string  := "ULTRASCALE"; --! "VIRTEX6", "7SERIES", "ULTRASCALE"
        SINGLE_LANE : boolean := false -- Enable single lane mode PCS (10G, 25G mode)
    );
    port (
        RESET_PCS  : in std_logic;
        CLK        : in std_logic; -- TX clock, 156.25MHz
        XLGMII_TXD : in std_logic_vector(255 downto 0); -- TX data
        XLGMII_TXC : in std_logic_vector(31 downto 0);  -- TX command
        -- Control
        SCR_BYPASS : in std_logic; -- scrambler bypass
        ENC_BYPASS : in std_logic; -- 64/66 encoder bypass
        -- PMA interface
        RESET_PMA  : in std_logic;
        TXCLK      : in std_logic; -- GTY clock 161.1328125 MHz
        TXREADY    : in std_logic_vector(3 downto 0); --
        TXD0       : out std_logic_vector(65 downto 0); -- TX data for PMA, lane 0
        TXD1       : out std_logic_vector(65 downto 0); -- TX data for PMA, lane 1
        TXD2       : out std_logic_vector(65 downto 0); -- TX data for PMA, lane 2
        TXD3       : out std_logic_vector(65 downto 0); -- TX data for PMA, lane 3
        -- Debug
        TXD_O      : out std_logic_vector(4*66-1 downto 0);
        DEBUG_V    : out std_logic_vector(15 downto 0)
    );
end tx_path_40g;

-- ----------------------------------------------------------------------------
--             Architecture declaration
-- ----------------------------------------------------------------------------
architecture structural of tx_path_40g is

    constant NUM_LANES : natural := 4;

    signal encoded_data  : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal zeros         : std_logic_vector(127 downto 0);
    signal data_to_scr   : std_logic_vector(64*NUM_LANES-1 downto 0);
    signal data_from_scr : std_logic_vector(64*NUM_LANES-1 downto 0);
    signal txdata_scr    : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal txdata_scr_am : std_logic_vector(66*NUM_LANES-1 downto 0);
    signal fifo_rd_en    : std_logic;
    signal am_rd_en      : std_logic;
    signal data_from_fifo: std_logic_vector(66*NUM_LANES-1 downto 0);
    signal hdr_from_fifo : std_logic_vector(2*NUM_LANES-1 downto 0);

    signal enc_bypass_sync : std_logic;
    signal scr_bypass_sync : std_logic;

begin

zeros <= (others => '0');

    -- Control/status clock domain crossing --------------------------------------
    CROSS_ENC_BYP: entity work.ASYNC_OPEN_LOOP
    generic map(IN_REG  => false, TWO_REG => true)
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => ENC_BYPASS,
        --
        BCLK     => CLK,
        BRST     => '0',
        BDATAOUT => enc_bypass_sync
    );

    CROSS_SCR_BYP: entity work.ASYNC_OPEN_LOOP
    generic map(IN_REG  => false, TWO_REG => true)
    port map(
        ACLK     => '0',
        ARST     => '0',
        ADATAIN  => SCR_BYPASS,
        --
        BCLK     => TXCLK,
        BRST     => '0',
        BDATAOUT => scr_bypass_sync
    );

    -- =========================================================================
    -- 64/66 GBASE-R encoder
    -- =========================================================================
    encode_i: entity work.gbaser_encode
    generic map (
        LANES => 4
    )
    port map (
        RESET  => RESET_PCS,
        CLK    => clk,
        -- RS/MAC interface -------------------------
        D      => XLGMII_TXD,
        C      => XLGMII_TXC,
        -- PMA interface --------------------------
        TXD    => encoded_data
    );

    -- =========================================================================
    -- FIFO for removing IPG for aligment marker insertion
    -- =========================================================================
    TXFIFO: entity work.pcs_tx_fifo
    generic map (
        NUM_LANES => NUM_LANES,
        DEVICE    => DEVICE
    )
    port map (
        RESET_D => RESET_PCS,
        CLK     => CLK,
        D       => encoded_data,
        --
        RESET_Q => RESET_PMA,
        TXCLK   => TXCLK,
        RE      => fifo_rd_en,
        Q       => data_from_fifo,
        --
        FIFO_EMPTY_O => DEBUG_V(0),
        FIFO_FULL_O  => DEBUG_V(1),
        FIFO_DIN_O   => open, --TXD_O,
        DROP_O       => DEBUG_V(2),
        INDEX_O      => DEBUG_V(7 downto 4)
    );

    -- =========================================================================
    -- Scrambler
    -- =========================================================================
    GEN_SCR_DATA: for i in 0 to NUM_LANES-1 generate
        data_to_scr((i+1)*64-1 downto i*64) <= data_from_fifo(66*(i+1)-1 downto i*66+2);
    end generate;

    -- Single lane mode: store block headers for next use
    HDR_FFS_G: if SINGLE_LANE generate
        HDR_FFS: process(TXCLK)
        begin
            if TXCLK'event and TXCLK = '1' then
                for i in 0 to NUM_LANES-1 loop
                    if fifo_rd_en = '1' then
                        hdr_from_fifo(i*2+1 downto i*2) <= data_from_fifo(66*i+1 downto 66*i);
                    end if;
                end loop;
            end if;
        end process;
    end generate;

    -- Single lane mode - do not store headers to FFs
    NO_HDR_FFS_G: if (not SINGLE_LANE) generate
        HDRS: for i in 0 to NUM_LANES-1 generate
            hdr_from_fifo(i*2+1 downto i*2) <= data_from_fifo(66*i+1 downto 66*i);
        end generate;
    end generate;

    SCRAMBLE: entity work.scrambler_gen
    generic map (
        WIDTH => NUM_LANES*64,
        OREG  => SINGLE_LANE
    )
    port map (
        RESET  => RESET_PMA,
        CLK    => TXCLK,
        EN     => fifo_rd_en,
        BYPASS => scr_bypass_sync,
        SEED   => zeros(57 downto 0),
        D      => data_to_scr,
        Q      => data_from_scr
    );

    -- =========================================================================
    -- Alignment markers
    -- =========================================================================
    fifo_rd_en <= am_rd_en and TXREADY(0);

    GEN_TX_DATA: for i in 0 to NUM_LANES-1 generate
        txdata_scr(66*(i+1)-1 downto 66*i+2) <= data_from_scr(64*(i+1)-1 downto 64*i); -- 64-bit block payload
        txdata_scr(66*i+1 downto 66*i)       <= hdr_from_fifo(i*2+1 downto i*2);
    end generate;

    -- Multi lane PCS mode (insert alignment markers)
    AM_G: if (not SINGLE_LANE) generate
        -- Insert al. markers
        AM_INS: entity work.am_ins4
        port map (
            RESET => RESET_PMA,
            CLK   => TXCLK,
            RD    => am_rd_en,
            EN    => TXREADY(0),
            D     => txdata_scr,
            Q     => txdata_scr_am
        );
    end generate;

    -- Single lane mode (no allignment markers)
    NO_AM_G: if (SINGLE_LANE) generate
        am_rd_en      <= '1';
        txdata_scr_am <= txdata_scr;
    end generate;

    -- =========================================================================
    -- Others
    -- =========================================================================
    TXD0 <= txdata_scr_am(66*1-1 downto 66*0);
    TXD1 <= txdata_scr_am(66*2-1 downto 66*1);
    TXD2 <= txdata_scr_am(66*3-1 downto 66*2);
    TXD3 <= txdata_scr_am(66*4-1 downto 66*3);

    TXD_O <= data_from_fifo;
    DEBUG_V(3) <= fifo_rd_en;

end structural;
