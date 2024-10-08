-- Copyright (C) 2018 CESNET
-- Author(s): Mario Kuka <kuka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TX_DMA_EXTRACTOR is
    generic (
        -- true:  use full implementation of component. Remove sze header(first 8 bytes) from incoming packets from txdma.
        -- false: use blank implementation. Send RX to TX without modification. IFC is zero constant.
        SUPPORT         : boolean := true;
        -- size of fifo on IFC output interface
        IFC_FIFO_SIZE   : integer := 64;
        -- size of fifo on TX flu interface
        TX_FIFO_SIZE    : integer := 4;
        -- \brief Data width of FLU data convey bus.
        -- \description Supported values are powers of 2 greater than 32.
        DATA_WIDTH      : integer := 512;
        -- \brief Width of sop_pos signal from FLU bus (see FLU spec).
        -- \description Commonly used value is log2(DATA_WIDTH/64), but can be anything from 1 to log2(DATA_WIDTH/8).
        SOP_POS_WIDTH   : integer := 3;
        -- "ULTRASCALE" (Xilinx)
        -- "7SERIES"    (Xilinx)
        -- "ARRIA10"    (Intel)
        -- "STRATIX10"  (Intel)
        DEVICE          : string  := "ULTRASCALE"
    );
    port(
        CLK         : in  std_logic;
        RESET       : in  std_logic;
        -- RX
        RX_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_SOP_POS  : in  std_logic_vector(SOP_POS_WIDTH-1 downto 0);
        RX_EOP_POS  : in  std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        RX_SOP      : in  std_logic;
        RX_EOP      : in  std_logic;
        RX_SRC_RDY  : in  std_logic;
        RX_DST_RDY  : out std_logic;
        -- TX
        TX_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        TX_SOP_POS  : out std_logic_vector(SOP_POS_WIDTH-1 downto 0);
        TX_EOP_POS  : out std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
        TX_SOP      : out std_logic;
        TX_EOP      : out std_logic;
        TX_SRC_RDY  : out std_logic;
        TX_DST_RDY  : in  std_logic;
        -- OUTPUT: selected interface
        IFC         : out std_logic_vector(7 downto 0);
        IFC_SRC_RDY : out std_logic;
        IFC_DST_RDY : in  std_logic
    );
end entity;

