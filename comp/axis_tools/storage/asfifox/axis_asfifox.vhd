-- axis_asfifox.vhd: AXI-Stream ASFIFOX
-- Copyright (C) 2024 CESNET
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

--
entity AXIS_ASFIFOX is
    generic (
        -- Width of AXI-Stream data signal in bits.
        TDATA_WIDTH   : natural := 512;
        -- Width of AXI-Stream user signal in bits.
        TUSER_WIDTH   : natural := 64;
        -- FIFO depth in number of data words, must be power of two!
        -- Minimum value is 2.
        FIFO_ITEMS    : natural := 512;
        -- Select memory implementation. Options:
        -- "LUT"  - effective for shallow FIFO (approx. ITEMS <= 64),
        -- "BRAM" - effective for deep FIFO (approx. ITEMS > 64).
        RAM_TYPE      : string  := "BRAM";
        -- First Word Fall Through mode. If FWFT_MODE=True, valid data will be
        -- ready at the ASFIFOX output without TX_AXIS_TREADY requests.
        FWFT_MODE     : boolean := True;
        -- Enabled output registers allow better timing for a few flip-flops.
        OUTPUT_REG    : boolean := True;
        -- Sets the maximum number of remaining free data words in the ASFIFOX
        -- that triggers the RX_FIFO_AFULL signal.
        AFULL_OFFSET  : natural := FIFO_ITEMS/2;
        -- Sets the maximum number of data words stored in the ASFIFOX that
        -- triggers the TX_FIFO_AEMPTY signal.
        AEMPTY_OFFSET : natural := FIFO_ITEMS/2;
        -- Target device: AGILEX, STRATIX10, ULTRASCALE,...
        DEVICE        : string  := "AGILEX"
    );
    port (
        -- =========================================================================
        -- RX AXI-Stream interface (RX_CLK)
        -- =========================================================================
        RX_CLK         : in  std_logic;
        RX_RESET       : in  std_logic;

        RX_AXIS_TDATA  : in  std_logic_vector(TDATA_WIDTH-1 downto 0);
        RX_AXIS_TUSER  : in  std_logic_vector(TUSER_WIDTH-1 downto 0);
        RX_AXIS_TKEEP  : in  std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        RX_AXIS_TLAST  : in  std_logic;
        RX_AXIS_TVALID : in  std_logic;
        RX_AXIS_TREADY : out std_logic;

        RX_FIFO_AFULL  : out std_logic;
        RX_FIFO_STATUS : out std_logic_vector(log2(FIFO_ITEMS) downto 0);

        -- =========================================================================
        -- TX AXI-Stream interface (TX_CLK)
        -- =========================================================================
        TX_CLK         : in  std_logic;
        TX_RESET       : in  std_logic;

        TX_AXIS_TDATA  : out std_logic_vector(TDATA_WIDTH-1 downto 0);
        TX_AXIS_TUSER  : out std_logic_vector(TUSER_WIDTH-1 downto 0);
        TX_AXIS_TKEEP  : out std_logic_vector(TDATA_WIDTH/8-1 downto 0);
        TX_AXIS_TLAST  : out std_logic;
        TX_AXIS_TVALID : out std_logic;
        TX_AXIS_TREADY : in  std_logic;

        TX_FIFO_AEMPTY : out std_logic;
        TX_FIFO_STATUS : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
    );
end entity;

architecture FULL of AXIS_ASFIFOX is

    constant FIFO_DW  : natural := TDATA_WIDTH+TUSER_WIDTH+(TDATA_WIDTH/8)+1;

    signal fifo_di    : std_logic_vector(FIFO_DW-1 downto 0);
    signal fifo_do    : std_logic_vector(FIFO_DW-1 downto 0);
    signal fifo_full  : std_logic;
    signal fifo_empty : std_logic;

begin

    fifo_di        <= RX_AXIS_TDATA & RX_AXIS_TUSER & RX_AXIS_TKEEP & RX_AXIS_TLAST;
    RX_AXIS_TREADY <= not fifo_full;

    asfifox_i : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => FIFO_DW,
        ITEMS               => FIFO_ITEMS,
        RAM_TYPE            => RAM_TYPE,
        FWFT_MODE           => FWFT_MODE,
        OUTPUT_REG          => OUTPUT_REG,
        DEVICE              => DEVICE,
        ALMOST_FULL_OFFSET  => AFULL_OFFSET,
        ALMOST_EMPTY_OFFSET => AEMPTY_OFFSET
    ) port map (
        WR_CLK    => RX_CLK,
        WR_RST    => RX_RESET,

        WR_DATA   => fifo_di,
        WR_EN     => RX_AXIS_TVALID,
        WR_FULL   => fifo_full,
        WR_AFULL  => RX_FIFO_AFULL,
        WR_STATUS => RX_FIFO_STATUS,

        RD_CLK    => TX_CLK,
        RD_RST    => TX_RESET,

        RD_DATA   => fifo_do,
        RD_EN     => TX_AXIS_TREADY,
        RD_EMPTY  => fifo_empty,
        RD_AEMPTY => TX_FIFO_AEMPTY,
        RD_STATUS => TX_FIFO_STATUS
    );

    TX_AXIS_TDATA  <= fifo_do(FIFO_DW-1 downto TUSER_WIDTH+(TDATA_WIDTH/8)+1);
    TX_AXIS_TUSER  <= fifo_do(TUSER_WIDTH+(TDATA_WIDTH/8)+1-1 downto (TDATA_WIDTH/8)+1);
    TX_AXIS_TKEEP  <= fifo_do((TDATA_WIDTH/8)+1-1 downto 1);
    TX_AXIS_TLAST  <= fifo_do(0);

    TX_AXIS_TVALID <= not fifo_empty;

end architecture;
