-- mvb_asfifox.vhd: MVB ASFIFOX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_misc.all;
use work.math_pack.all;

entity MVB_ASFIFOX is
    generic(
        -- Number of ITEMS in one Word
        MVB_ITEMS                   : integer := 4;
        -- Width of one MVB item
        -- any possitive value
        MVB_ITEM_WIDTH              : integer := 8;
        -- FIFO depth in number of data words, must be power of two!
        -- Minimum value is 2.
        FIFO_ITEMS               : natural := 512;
        -- Select memory implementation. Options:
        -- "LUT"  - effective for shallow FIFO (approx. ITEMS <= 64),
        -- "BRAM" - effective for deep FIFO (approx. ITEMS > 64).
        RAM_TYPE            : string  := "BRAM";
        -- First Word Fall Through mode. If FWFT_MODE=True, valid data will be
        -- ready at the ASFIFOX output without RD_EN requests.
        FWFT_MODE           : boolean := True;
        -- Enabled output registers allow better timing for a few flip-flops.
        OUTPUT_REG          : boolean := True;
        -- The DEVICE parameter is ignored in the current component version.
        -- It can be used in the future.
        DEVICE              : string  := "ULTRASCALE";
        -- Sets the maximum number of remaining free data words in the ASFIFOX
        -- that triggers the WR_AFULL signal.
        ALMOST_FULL_OFFSET  : natural := FIFO_ITEMS/2;
        -- Sets the maximum number of data words stored in the ASFIFOX that
        -- triggers the RD_AEMPTY signal.
        ALMOST_EMPTY_OFFSET : natural := FIFO_ITEMS/2
    );
    port(
        RX_CLK        : in  std_logic;
        RX_RESET      : in  std_logic;

        RX_DATA       : in  std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_VLD        : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_SRC_RDY    : in  std_logic;
        RX_DST_RDY    : out std_logic;
        RX_AFULL      : out std_logic;
        RX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0);

        TX_CLK        : in  std_logic;
        TX_RESET      : in  std_logic;

        TX_DATA       : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_SRC_RDY    : out std_logic;
        TX_DST_RDY    : in  std_logic;
        TX_AEMPTY     : out std_logic;
        TX_STATUS     : out std_logic_vector(log2(FIFO_ITEMS) downto 0)
    );
end entity;



architecture full of MVB_ASFIFOX is

    signal di, do : std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto 0);

    signal full, empty : std_logic;

begin

    fifo_core : entity work.ASFIFOX
    generic map (
        DATA_WIDTH          => MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS,
        ITEMS               => FIFO_ITEMS         ,
        RAM_TYPE            => RAM_TYPE           ,
        FWFT_MODE           => FWFT_MODE          ,
        OUTPUT_REG          => OUTPUT_REG         ,
        DEVICE              => DEVICE             ,
        ALMOST_FULL_OFFSET  => ALMOST_FULL_OFFSET ,
        ALMOST_EMPTY_OFFSET => ALMOST_EMPTY_OFFSET
    ) port map (
        WR_CLK    => RX_CLK    ,
        WR_RST    => RX_RESET  ,

        WR_DATA   => di        ,
        WR_EN     => RX_SRC_RDY,
        WR_FULL   => full      ,
        WR_AFULL  => RX_AFULL  ,
        WR_STATUS => RX_STATUS ,

        RD_CLK    => TX_CLK    ,
        RD_RST    => TX_RESET  ,

        RD_DATA   => do        ,
        RD_EN     => TX_DST_RDY,
        RD_EMPTY  => empty     ,
        RD_AEMPTY => TX_AEMPTY ,
        RD_STATUS => TX_STATUS
    );

    di <= RX_DATA & RX_VLD;
    RX_DST_RDY <= not full;

    TX_VLD     <= do(MVB_ITEMS-1 downto 0);
    TX_DATA    <= do(MVB_ITEMS*MVB_ITEM_WIDTH+MVB_ITEMS-1 downto MVB_ITEMS);
    TX_SRC_RDY <= not empty;

end architecture;
