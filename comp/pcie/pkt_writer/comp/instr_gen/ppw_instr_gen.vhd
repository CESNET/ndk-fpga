-- Copyright (C) 2025 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;


-- This module prepares instructions for the PPW_BREAKER.
-- It accepts original packet Address and Length and, according to packet boundaries, it splits them into multiple transactions with adjusted addresses and lengths.
-- Last transaction for a packet is indicated by the LAST signal (this and all previous instructions belong to a single packet on MFB).
--
-- Is able to transfer metadata: metadata of the original instruction are duplicated for all partial instructions.
--
entity PPW_INSTR_GEN is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS      : natural := 1;
        MVB_META_WIDTH : natural := 0;
        -- Maximum packet size (in bytes).
        PKT_MTU        : integer := 2**12;
        PCIE_MPS_WIDTH : integer := 15;
        ADDRESS_WIDTH  : natural := 64;
        -- Size of a RAM page (in bytes).
        PAGE_SIZE      : natural := 4096;
        DEVICE         : string := "AGILEX"
    );
    port (
        CLK            : in std_logic;
        RESET          : in std_logic;

        -- Specifies the currently configured PCIe Maximum Packet Size (in bytes).
        -- PCIe specification allows at least 128.
        PCIE_MPS       : in  std_logic_vector(PCIE_MPS_WIDTH-1 downto 0);

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_META    : in  std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0) := (others => '0');
        RX_MVB_ADDRESS : in  std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        RX_MVB_LENGTH  : in  std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VALID   : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic;
        RX_MVB_DST_RDY : out std_logic;

        -- ========================================================
        -- TX Interface
        -- ========================================================

        TX_MVB_META    : out std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
        TX_MVB_ADDRESS : out std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
        TX_MVB_LENGTH  : out std_logic_vector(MVB_ITEMS*PCIE_MPS_WIDTH-1 downto 0);
        -- Indicates final MVB Item for a packet.
        TX_MVB_LAST    : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VALID   : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of PPW_INSTR_GEN is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal mvb_meta        : std_logic_vector(MVB_ITEMS*MVB_META_WIDTH-1 downto 0);
    signal mvb_address     : std_logic_vector(MVB_ITEMS*ADDRESS_WIDTH-1 downto 0);
    signal mvb_length      : std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
    signal mvb_last        : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_valid       : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal mvb_src_rdy     : std_logic;
    signal mvb_dst_rdy     : std_logic;

begin

    -- =====================================================================
    --  Page break planner
    -- =====================================================================

    page_break_planner_i : entity work.PPW_PAGE_BREAK_PLANNER
    generic map (
        MVB_ITEMS      => MVB_ITEMS,
        MVB_META_WIDTH => MVB_META_WIDTH,
        PKT_MTU        => PKT_MTU,
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        PAGE_SIZE      => PAGE_SIZE,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MVB_META    => RX_MVB_META,
        RX_MVB_ADDRESS => RX_MVB_ADDRESS,
        RX_MVB_LENGTH  => RX_MVB_LENGTH,
        RX_MVB_VALID   => RX_MVB_VALID,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY,

        TX_MVB_META    => mvb_meta,
        TX_MVB_ADDRESS => mvb_address,
        TX_MVB_LENGTH  => mvb_length,
        TX_MVB_LAST    => mvb_last,
        TX_MVB_VALID   => mvb_valid,
        TX_MVB_SRC_RDY => mvb_src_rdy,
        TX_MVB_DST_RDY => mvb_dst_rdy
    );

    -- =====================================================================
    --  MTU break planner
    -- =====================================================================

    mtu_break_planner_i : entity work.PPW_MTU_BREAK_PLANNER
    generic map (
        MVB_ITEMS      => MVB_ITEMS,
        MVB_META_WIDTH => MVB_META_WIDTH,
        PKT_MTU        => PKT_MTU,
        ADDRESS_WIDTH  => ADDRESS_WIDTH,
        PCIE_MPS_WIDTH => PCIE_MPS_WIDTH,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        PCIE_MPS       => PCIE_MPS,

        RX_MVB_META    => mvb_meta,
        RX_MVB_ADDRESS => mvb_address,
        RX_MVB_LENGTH  => mvb_length,
        RX_MVB_LAST    => mvb_last,
        RX_MVB_VALID   => mvb_valid,
        RX_MVB_SRC_RDY => mvb_src_rdy,
        RX_MVB_DST_RDY => mvb_dst_rdy,

        TX_MVB_META    => TX_MVB_META,
        TX_MVB_ADDRESS => TX_MVB_ADDRESS,
        TX_MVB_LENGTH  => TX_MVB_LENGTH,
        TX_MVB_LAST    => TX_MVB_LAST,
        TX_MVB_VALID   => TX_MVB_VALID,
        TX_MVB_SRC_RDY => TX_MVB_SRC_RDY,
        TX_MVB_DST_RDY => TX_MVB_DST_RDY
    );

end architecture;
