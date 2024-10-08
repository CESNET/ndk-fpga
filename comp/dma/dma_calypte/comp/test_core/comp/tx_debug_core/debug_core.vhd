-- debug_core.vhd: For debugging the traffic coming from the TX DMA Calypte
-- Copyright (C) 2023 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;


entity TX_DMA_DEBUG_CORE is
    generic(
        DEVICE : string := "ULTRASCALE";

        MFB_REGIONS     : natural := 1;
        MFB_REGION_SIZE : natural := 4;
        MFB_BLOCK_SIZE  : natural := 8;
        MFB_ITEM_WIDTH  : natural := 8;

        DMA_META_WIDTH : natural := 24;
        PKT_SIZE_MAX   : natural := 2**16-1;
        CHANNELS       : natural := 4;

        DBG_CNTRS_WIDTH : natural := 64;
        ST_SP_DBG_SIGNAL_W : natural := 2;

        -- Width of MI bus
        MI_WIDTH    : natural := 32;
        MI_SAME_CLK : boolean := FALSE
        );
    port(
        -- =======================================================================
        -- CLOCK AND RESET
        -- =======================================================================
        CLK   : in std_logic;
        RESET : in std_logic;

        -- =========================================================================================
        -- Various other debug interfaces
        -- =========================================================================================
        ST_SP_DBG_CHAN : in std_logic_vector(log2(CHANNELS) -1 downto 0);
        ST_SP_DBG_META : in std_logic_vector(ST_SP_DBG_SIGNAL_W - 1 downto 0);

        -- =======================================================================
        -- RX MFB INTERFACE
        -- =======================================================================
        RX_MFB_META_PKT_SIZE : in std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);
        RX_MFB_META_CHAN     : in std_logic_vector(log2(CHANNELS) -1 downto 0);
        RX_MFB_META_HDR_META : in std_logic_vector(DMA_META_WIDTH -1 downto 0);

        RX_MFB_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =======================================================================
        -- TX MFB INTERFACE
        -- =======================================================================
        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*(DMA_META_WIDTH+log2(CHANNELS)+log2(PKT_SIZE_MAX+1))-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1, log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic;

        -- =====================================================================
        -- MI interface for SW access
        -- =====================================================================
        MI_CLK   : in std_logic;
        MI_RESET : in std_logic;

        MI_ADDR : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_DWR  : in  std_logic_vector(MI_WIDTH-1 downto 0);
        MI_BE   : in  std_logic_vector(MI_WIDTH/8-1 downto 0);
        MI_RD   : in  std_logic;
        MI_WR   : in  std_logic;
        MI_DRD  : out std_logic_vector(MI_WIDTH-1 downto 0);
        MI_ARDY : out std_logic;
        MI_DRDY : out std_logic
        );
end entity;

architecture FULL of TX_DMA_DEBUG_CORE is

    constant CNT_NUM : natural := 11;

    -- Total number of registers
    constant REGS : natural := CNT_NUM*2;

    -- Width of address for registers within one DMA Channel
    constant REG_ADDR_WIDTH : natural := 7;

    -- Assigns an index to each register name --
    -- Counter of correct lengths of the packets
    constant R_CNT_CORR_PKT_LENGTHS_L : natural := 0;
    constant R_CNT_CORR_PKT_LENGTHS_H : natural := 1;
    -- Counter of bad lengths of the packets
    constant R_CNT_BAD_PKT_LENGTHS_L  : natural := 2;
    constant R_CNT_BAD_PKT_LENGTHS_H  : natural := 3;
    -- Counter of length-checker overflows
    constant R_CNT_FR_LEN_OVF_L       : natural := 4;
    constant R_CNT_FR_LEN_OVF_H       : natural := 5;
    -- Counter of DMA headers comming out of order (not preceded by packet data)
    constant R_CNT_HDR_OUT_ORD_L      : natural := 6;
    constant R_CNT_HDR_OUT_ORD_H      : natural := 7;
    -- Counter of total number of DMA headers
    constant R_CNT_DMA_HDR_NUM_L      : natural := 8;
    constant R_CNT_DMA_HDR_NUM_H      : natural := 9;
    -- Counter of correct lengths counted from PCIe transactions
    constant R_CNT_PCIE_LNG_CORR_L    : natural := 10;
    constant R_CNT_PCIE_LNG_CORR_H    : natural := 11;
    -- Counter of incorrect lengths counted from PCIe transactions
    constant R_CNT_PCIE_LNG_INCORR_L  : natural := 12;
    constant R_CNT_PCIE_LNG_INCORR_H  : natural := 13;
    -- Counter of matched patterns in the pattern checker
    constant R_CNT_PTRN_MATCH_L       : natural := 14;
    constant R_CNT_PTRN_MATCH_H       : natural := 15;
    -- Counter of MISmatched patterns in the pattern checker
    constant R_CNT_PTRN_MISMATCH_L    : natural := 16;
    constant R_CNT_PTRN_MISMATCH_H    : natural := 17;
    -- Counter of matched patterns from the DMA header in the pattern checker
    constant R_CNT_META_PTRN_MATCH_L  : natural := 18;
    constant R_CNT_META_PTRN_MATCH_H  : natural := 19;
    -- Counter of MISmatched patterns from the DMA header in the pattern checker
    constant R_CNT_META_PTRN_MISMATCH_L : natural := 20;
    constant R_CNT_META_PTRN_MISMATCH_H : natural := 21;

    -- MI address space for each DMA Channel
    constant R_ADDRS : n_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => 16#00#,
        R_CNT_CORR_PKT_LENGTHS_H => 16#04#,

        R_CNT_BAD_PKT_LENGTHS_L  => 16#08#,
        R_CNT_BAD_PKT_LENGTHS_H  => 16#0C#,

        R_CNT_FR_LEN_OVF_L       => 16#10#,
        R_CNT_FR_LEN_OVF_H       => 16#14#,

        R_CNT_HDR_OUT_ORD_L      => 16#18#,
        R_CNT_HDR_OUT_ORD_H      => 16#1C#,

        R_CNT_DMA_HDR_NUM_L      => 16#20#,
        R_CNT_DMA_HDR_NUM_H      => 16#24#,

        R_CNT_PCIE_LNG_CORR_L    => 16#28#,
        R_CNT_PCIE_LNG_CORR_H    => 16#2C#,

        R_CNT_PCIE_LNG_INCORR_L  => 16#30#,
        R_CNT_PCIE_LNG_INCORR_H  => 16#34#,

        R_CNT_PTRN_MATCH_L       => 16#38#,
        R_CNT_PTRN_MATCH_H       => 16#3C#,

        R_CNT_PTRN_MISMATCH_L    => 16#40#,
        R_CNT_PTRN_MISMATCH_H    => 16#44#,

        R_CNT_META_PTRN_MATCH_L  => 16#48#,
        R_CNT_META_PTRN_MATCH_H  => 16#4C#,

        R_CNT_META_PTRN_MISMATCH_L => 16#50#,
        R_CNT_META_PTRN_MISMATCH_H => 16#54#
        );
    --------

    -- Strobe enable
    -- (set to True for counter registers, which are only updated from counters
    --  by writing 1 from MI and reset by writing 0)
    constant STROBE_EN : b_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => TRUE,
        R_CNT_CORR_PKT_LENGTHS_H => TRUE,
        R_CNT_BAD_PKT_LENGTHS_L  => TRUE,
        R_CNT_BAD_PKT_LENGTHS_H  => TRUE,
        R_CNT_FR_LEN_OVF_L       => TRUE,
        R_CNT_FR_LEN_OVF_H       => TRUE,
        R_CNT_HDR_OUT_ORD_L      => TRUE,
        R_CNT_HDR_OUT_ORD_H      => TRUE,
        R_CNT_DMA_HDR_NUM_L      => TRUE,
        R_CNT_DMA_HDR_NUM_H      => TRUE,
        R_CNT_PCIE_LNG_CORR_L    => TRUE,
        R_CNT_PCIE_LNG_CORR_H    => TRUE,
        R_CNT_PCIE_LNG_INCORR_L  => TRUE,
        R_CNT_PCIE_LNG_INCORR_H  => TRUE,
        R_CNT_PTRN_MATCH_L       => TRUE,
        R_CNT_PTRN_MATCH_H       => TRUE,
        R_CNT_PTRN_MISMATCH_L    => TRUE,
        R_CNT_PTRN_MISMATCH_H    => TRUE,
        R_CNT_META_PTRN_MATCH_L  => TRUE,
        R_CNT_META_PTRN_MATCH_H  => TRUE,
        R_CNT_META_PTRN_MISMATCH_L => TRUE,
        R_CNT_META_PTRN_MISMATCH_H => TRUE
        );

    -- Write enable (set to False for read-only registers)
    -- Must be set to True, when the coresponding index in STROBE_EN is True
    constant WR_EN : b_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => FALSE or STROBE_EN(R_CNT_CORR_PKT_LENGTHS_L),
        R_CNT_CORR_PKT_LENGTHS_H => FALSE or STROBE_EN(R_CNT_CORR_PKT_LENGTHS_H),
        R_CNT_BAD_PKT_LENGTHS_L  => FALSE or STROBE_EN(R_CNT_BAD_PKT_LENGTHS_L),
        R_CNT_BAD_PKT_LENGTHS_H  => FALSE or STROBE_EN(R_CNT_BAD_PKT_LENGTHS_H),
        R_CNT_FR_LEN_OVF_L       => FALSE or STROBE_EN(R_CNT_FR_LEN_OVF_L),
        R_CNT_FR_LEN_OVF_H       => FALSE or STROBE_EN(R_CNT_FR_LEN_OVF_H),
        R_CNT_HDR_OUT_ORD_L      => FALSE or STROBE_EN(R_CNT_HDR_OUT_ORD_L),
        R_CNT_HDR_OUT_ORD_H      => FALSE or STROBE_EN(R_CNT_HDR_OUT_ORD_H),
        R_CNT_DMA_HDR_NUM_L      => FALSE or STROBE_EN(R_CNT_DMA_HDR_NUM_L),
        R_CNT_DMA_HDR_NUM_H      => FALSE or STROBE_EN(R_CNT_DMA_HDR_NUM_H),
        R_CNT_PCIE_LNG_CORR_L    => FALSE or STROBE_EN(R_CNT_PCIE_LNG_CORR_L),
        R_CNT_PCIE_LNG_CORR_H    => FALSE or STROBE_EN(R_CNT_PCIE_LNG_CORR_H),
        R_CNT_PCIE_LNG_INCORR_L  => FALSE or STROBE_EN(R_CNT_PCIE_LNG_INCORR_L),
        R_CNT_PCIE_LNG_INCORR_H  => FALSE or STROBE_EN(R_CNT_PCIE_LNG_INCORR_H),
        R_CNT_PTRN_MATCH_L       => FALSE or STROBE_EN(R_CNT_PTRN_MATCH_L),
        R_CNT_PTRN_MATCH_H       => FALSE or STROBE_EN(R_CNT_PTRN_MATCH_H),
        R_CNT_PTRN_MISMATCH_L    => FALSE or STROBE_EN(R_CNT_PTRN_MISMATCH_L),
        R_CNT_PTRN_MISMATCH_H    => FALSE or STROBE_EN(R_CNT_PTRN_MISMATCH_H),
        R_CNT_META_PTRN_MATCH_L  => FALSE or STROBE_EN(R_CNT_META_PTRN_MATCH_L),
        R_CNT_META_PTRN_MATCH_H  => FALSE or STROBE_EN(R_CNT_META_PTRN_MATCH_H),
        R_CNT_META_PTRN_MISMATCH_L => FALSE or STROBE_EN(R_CNT_META_PTRN_MISMATCH_L),
        R_CNT_META_PTRN_MISMATCH_H => FALSE or STROBE_EN(R_CNT_META_PTRN_MISMATCH_H)
        );

    -- Actual number of needed write ports for each register
    -- Must be at least 1 for all registers with Write Enable
    constant WR_PORTS : i_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => tsel(WR_EN(R_CNT_CORR_PKT_LENGTHS_L), 1, 0) + 0,
        R_CNT_CORR_PKT_LENGTHS_H => tsel(WR_EN(R_CNT_CORR_PKT_LENGTHS_H), 1, 0) + 0,
        R_CNT_BAD_PKT_LENGTHS_L  => tsel(WR_EN(R_CNT_BAD_PKT_LENGTHS_L), 1, 0) + 0,
        R_CNT_BAD_PKT_LENGTHS_H  => tsel(WR_EN(R_CNT_BAD_PKT_LENGTHS_H), 1, 0) + 0,
        R_CNT_FR_LEN_OVF_L       => tsel(WR_EN(R_CNT_FR_LEN_OVF_L), 1, 0) + 0,
        R_CNT_FR_LEN_OVF_H       => tsel(WR_EN(R_CNT_FR_LEN_OVF_H), 1, 0) + 0,
        R_CNT_HDR_OUT_ORD_L      => tsel(WR_EN(R_CNT_HDR_OUT_ORD_L), 1, 0) + 0,
        R_CNT_HDR_OUT_ORD_H      => tsel(WR_EN(R_CNT_HDR_OUT_ORD_H), 1, 0) + 0,
        R_CNT_DMA_HDR_NUM_L      => tsel(WR_EN(R_CNT_DMA_HDR_NUM_L), 1, 0) + 0,
        R_CNT_DMA_HDR_NUM_H      => tsel(WR_EN(R_CNT_DMA_HDR_NUM_H), 1, 0) + 0,
        R_CNT_PCIE_LNG_CORR_L    => tsel(WR_EN(R_CNT_PCIE_LNG_CORR_L), 1, 0) + 0,
        R_CNT_PCIE_LNG_CORR_H    => tsel(WR_EN(R_CNT_PCIE_LNG_CORR_H), 1, 0) + 0,
        R_CNT_PCIE_LNG_INCORR_L  => tsel(WR_EN(R_CNT_PCIE_LNG_INCORR_L), 1, 0) + 0,
        R_CNT_PCIE_LNG_INCORR_H  => tsel(WR_EN(R_CNT_PCIE_LNG_INCORR_H), 1, 0) + 0,
        R_CNT_PTRN_MATCH_L       => tsel(WR_EN(R_CNT_PTRN_MATCH_L), 1, 0) + 0,
        R_CNT_PTRN_MATCH_H       => tsel(WR_EN(R_CNT_PTRN_MATCH_H), 1, 0) + 0,
        R_CNT_PTRN_MISMATCH_L    => tsel(WR_EN(R_CNT_PTRN_MISMATCH_L), 1, 0) + 0,
        R_CNT_PTRN_MISMATCH_H    => tsel(WR_EN(R_CNT_PTRN_MISMATCH_H), 1, 0) + 0,
        R_CNT_META_PTRN_MATCH_L  => tsel(WR_EN(R_CNT_META_PTRN_MATCH_L), 1, 0) + 0,
        R_CNT_META_PTRN_MATCH_H  => tsel(WR_EN(R_CNT_META_PTRN_MATCH_H), 1, 0) + 0,
        R_CNT_META_PTRN_MISMATCH_L => tsel(WR_EN(R_CNT_META_PTRN_MISMATCH_L), 1, 0) + 0,
        R_CNT_META_PTRN_MISMATCH_H => tsel(WR_EN(R_CNT_META_PTRN_MISMATCH_H), 1, 0) + 0
        );

    -- Actual number of needed read ports for each register
    -- Must be at least one for all registers because one port is always
    -- dedicated for a read on the MI side
    constant RD_PORTS : i_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => 1 + 0,
        R_CNT_CORR_PKT_LENGTHS_H => 1 + 0,
        R_CNT_BAD_PKT_LENGTHS_L  => 1 + 0,
        R_CNT_BAD_PKT_LENGTHS_H  => 1 + 0,
        R_CNT_FR_LEN_OVF_L       => 1 + 0,
        R_CNT_FR_LEN_OVF_H       => 1 + 0,
        R_CNT_HDR_OUT_ORD_L      => 1 + 0,
        R_CNT_HDR_OUT_ORD_H      => 1 + 0,
        R_CNT_DMA_HDR_NUM_L      => 1 + 0,
        R_CNT_DMA_HDR_NUM_H      => 1 + 0,
        R_CNT_PCIE_LNG_CORR_L    => 1 + 0,
        R_CNT_PCIE_LNG_CORR_H    => 1 + 0,
        R_CNT_PCIE_LNG_INCORR_L  => 1 + 0,
        R_CNT_PCIE_LNG_INCORR_H  => 1 + 0,
        R_CNT_PTRN_MATCH_L       => 1 + 0,
        R_CNT_PTRN_MATCH_H       => 1 + 0,
        R_CNT_PTRN_MISMATCH_L    => 1 + 0,
        R_CNT_PTRN_MISMATCH_H    => 1 + 0,
        R_CNT_META_PTRN_MATCH_L  => 1 + 0,
        R_CNT_META_PTRN_MATCH_H  => 1 + 0,
        R_CNT_META_PTRN_MISMATCH_L => 1 + 0,
        R_CNT_META_PTRN_MISMATCH_H => 1 + 0
        );

    -- Write Byte Enable support for each register
    -- Only some registers supports write Byte Enable, since it
    -- means storing the register in mutliple LUTs with independent write ports
    constant WR_BE_SUPPORT : b_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => FALSE,
        R_CNT_CORR_PKT_LENGTHS_H => FALSE,
        R_CNT_BAD_PKT_LENGTHS_L  => FALSE,
        R_CNT_BAD_PKT_LENGTHS_H  => FALSE,
        R_CNT_FR_LEN_OVF_L       => FALSE,
        R_CNT_FR_LEN_OVF_H       => FALSE,
        R_CNT_HDR_OUT_ORD_L      => FALSE,
        R_CNT_HDR_OUT_ORD_H      => FALSE,
        R_CNT_DMA_HDR_NUM_L      => FALSE,
        R_CNT_DMA_HDR_NUM_H      => FALSE,
        R_CNT_PCIE_LNG_CORR_L    => FALSE,
        R_CNT_PCIE_LNG_CORR_H    => FALSE,
        R_CNT_PCIE_LNG_INCORR_L  => FALSE,
        R_CNT_PCIE_LNG_INCORR_H  => FALSE,
        R_CNT_PTRN_MATCH_L       => FALSE,
        R_CNT_PTRN_MATCH_H       => FALSE,
        R_CNT_PTRN_MISMATCH_L    => FALSE,
        R_CNT_PTRN_MISMATCH_H    => FALSE,
        R_CNT_META_PTRN_MATCH_L  => FALSE,
        R_CNT_META_PTRN_MATCH_H  => FALSE,
        R_CNT_META_PTRN_MISMATCH_L => FALSE,
        R_CNT_META_PTRN_MISMATCH_H => FALSE
        );

    -- True width of each register
    -- Only valid bits are propagated from LUTmems, others are forced to '0'.
    constant RD_WIDTH : i_array_t(REGS-1 downto 0) := (
        R_CNT_CORR_PKT_LENGTHS_L => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_CORR_PKT_LENGTHS_H => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_BAD_PKT_LENGTHS_L  => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_BAD_PKT_LENGTHS_H  => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_FR_LEN_OVF_L       => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_FR_LEN_OVF_H       => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_HDR_OUT_ORD_L      => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_HDR_OUT_ORD_H      => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_DMA_HDR_NUM_L      => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_DMA_HDR_NUM_H      => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_PCIE_LNG_CORR_L    => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_PCIE_LNG_CORR_H    => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_PCIE_LNG_INCORR_L  => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_PCIE_LNG_INCORR_H  => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_PTRN_MATCH_L       => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_PTRN_MATCH_H       => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_PTRN_MISMATCH_L    => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_PTRN_MISMATCH_H    => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_META_PTRN_MATCH_L  => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_META_PTRN_MATCH_H  => max(0, DBG_CNTRS_WIDTH-MI_WIDTH),
        R_CNT_META_PTRN_MISMATCH_L => minimum(MI_WIDTH, DBG_CNTRS_WIDTH),
        R_CNT_META_PTRN_MISMATCH_H => max(0, DBG_CNTRS_WIDTH-MI_WIDTH)
        );

    -- Maximum number of ports for setting width of signals
    constant WR_PORTS_MAX : natural := max(WR_PORTS);
    constant RD_PORTS_MAX : natural := max(RD_PORTS);

    -- Returns True when given address is an address of a register with STROBE enabled
    function isStrobeAddr(addr : integer) return boolean is
    begin
        for i in 0 to REGS-1 loop
            if (STROBE_EN(i) and R_ADDRS(i) = addr) then
                return TRUE;
            end if;
        end loop;
        return FALSE;
    end function;

    constant MI_SPLIT_PORTS : natural := 2;
    constant MI_SPLIT_BASES : slv_array_t(MI_SPLIT_PORTS-1 downto 0)(MI_WIDTH-1 downto 0) := (
        0 => X"00000000",   -- Counters
        1 => X"00008000");  -- MFB Generator
    constant MI_SPLIT_ADDR_MASK : std_logic_vector(MI_WIDTH -1 downto 0) := X"00008000";


    -- =============================================================================================
    -- MI Async
    -- =============================================================================================
    signal mi_sync_dwr  : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_sync_addr : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_sync_rd   : std_logic;
    signal mi_sync_wr   : std_logic;
    signal mi_sync_be   : std_logic_vector(MI_WIDTH/8 -1 downto 0);
    signal mi_sync_ardy : std_logic;
    signal mi_sync_drd  : std_logic_vector(MI_WIDTH -1 downto 0);
    signal mi_sync_drdy : std_logic;

    -- =====================================================================
    --  MI Splitter
    -- =====================================================================
    signal mi_split_addr : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_dwr  : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_be   : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH/8-1 downto 0);
    signal mi_split_rd   : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_wr   : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_drd  : slv_array_t(MI_SPLIT_PORTS -1 downto 0)(MI_WIDTH-1 downto 0);
    signal mi_split_ardy : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);
    signal mi_split_drdy : std_logic_vector(MI_SPLIT_PORTS -1 downto 0);

    signal mi_split_dwr_reg : std_logic_vector(MI_WIDTH-1 downto 0);

    -- =====================================================================
    --  MI interface logic
    -- =====================================================================
    signal mi_chan      : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal mi_chanI     : integer := 0;
    signal mi_chan_reg  : std_logic_vector(log2(CHANNELS)-1 downto 0);
    signal mi_reg_addr  : std_logic_vector(REG_ADDR_WIDTH-1 downto 0);
    signal mi_reg_addrI : integer := 0;


    -- =====================================================================
    --  MI register LUTRAMs
    -- =====================================================================
    signal reg_di    : slv_array_2d_t(REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0);
    signal reg_we    : slv_array_t (REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0);
    -- writing address
    signal reg_addra : slv_array_2d_t(REGS-1 downto 0)(WR_PORTS_MAX-1 downto 0)(log2(CHANNELS)-1 downto 0);
    -- reading address
    signal reg_addrb : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(log2(CHANNELS)-1 downto 0);
    signal reg_dob   : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0);
    signal cntr_do   : slv_array_t (REGS-1 downto 0)(MI_WIDTH-1 downto 0) := (others => (others => '0'));

    signal reg_dob_opt : slv_array_2d_t(REGS-1 downto 0)(RD_PORTS_MAX-1 downto 0)(MI_WIDTH-1 downto 0) := (others => (others => (others => '0')));

    -- =====================================================================
    --  Counters logic
    -- =====================================================================
    signal cntr_incr_chan : slv_array_t(CNT_NUM -1 downto 0)(log2(CHANNELS) -1 downto 0);
    signal cntr_incr_vld : std_logic_vector(CNT_NUM -1 downto 0);
    signal cntr_rst     : std_logic;
    signal cntr_rd      : std_logic;
    signal cntr_rd_val : slv_array_t(CNT_NUM -1 downto 0)(DBG_CNTRS_WIDTH-1 downto 0);

    signal cntr_rst_reg : std_logic;
    signal cntr_rd_reg  : std_logic;

    -- =============================================================================================
    -- Frame length checker
    -- =============================================================================================
    signal frame_chck_len : std_logic_vector(MFB_REGIONS*log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal frame_chck_len_ovf : std_logic_vector(MFB_REGIONS -1 downto 0);

    signal frame_len_stored : unsigned(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal frame_len_curr : unsigned(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal frame_chan_stored : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal frame_chan_curr : std_logic_vector(log2(CHANNELS) -1 downto 0);

    signal fr_lng_mfb_data    : std_logic_vector(TX_MFB_DATA'range);
    signal fr_lng_mfb_meta    : std_logic_vector(DMA_META_WIDTH + log2(CHANNELS) + log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal fr_lng_mfb_sof     : std_logic_vector(TX_MFB_SOF'range);
    signal fr_lng_mfb_eof     : std_logic_vector(TX_MFB_EOF'range);
    signal fr_lng_mfb_sof_pos : std_logic_vector(TX_MFB_SOF_POS'range);
    signal fr_lng_mfb_eof_pos : std_logic_vector(TX_MFB_EOF_POS'range);
    signal fr_lng_mfb_src_rdy : std_logic;
    signal fr_lng_mfb_dst_rdy : std_logic;

    -- =============================================================================================
    -- Pattern comparator
    -- =============================================================================================

    signal aux_sig_mfb_data    : std_logic_vector(TX_MFB_DATA'range);
    signal aux_sig_mfb_meta    : std_logic_vector(DMA_META_WIDTH + log2(CHANNELS) + log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal aux_sig_mfb_sof     : std_logic_vector(TX_MFB_SOF'range);
    signal aux_sig_mfb_eof     : std_logic_vector(TX_MFB_EOF'range);
    signal aux_sig_mfb_sof_pos : std_logic_vector(TX_MFB_SOF_POS'range);
    signal aux_sig_mfb_eof_pos : std_logic_vector(TX_MFB_EOF_POS'range);
    signal aux_sig_mfb_src_rdy : std_logic;
    signal aux_sig_mfb_dst_rdy : std_logic;

    signal aux_sig_mfb_item_vld : std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE -1 downto 0);

    type pattern_comp_state_t is (S_IDLE, S_COMP_MIDDLE_PKT);
    signal pattern_comp_pst : pattern_comp_state_t := S_IDLE;
    signal pattern_comp_nst : pattern_comp_state_t := S_IDLE;

    signal pattern_copy_val  : std_logic_vector(TX_MFB_DATA'range);
    signal comp_val_stored   : std_logic_vector(TX_MFB_DATA'range);
    signal comp_val_curr     : std_logic_vector(TX_MFB_DATA'range);
    signal comp_res_imm      : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal comp_res_reg      : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal comp_res_imm_vld  : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal comp_res_reg_vld  : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal comp_res_imm_diff : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal comp_res_reg_diff : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);

    signal pattern_match_cntr_incr    : std_logic;
    signal pattern_mismatch_cntr_incr : std_logic;

    signal meta_pattern_comp_pst : pattern_comp_state_t := S_IDLE;
    signal meta_pattern_comp_nst : pattern_comp_state_t := S_IDLE;

    signal meta_pattern_copy_val  : std_logic_vector(TX_MFB_DATA'range);
    signal meta_comp_val_stored   : std_logic_vector(TX_MFB_DATA'range);
    signal meta_comp_val_curr     : std_logic_vector(TX_MFB_DATA'range);
    signal meta_comp_res_imm      : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal meta_comp_res_reg      : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal meta_comp_res_imm_vld  : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal meta_comp_res_reg_vld  : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal meta_comp_res_imm_diff : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);
    signal meta_comp_res_reg_diff : std_logic_vector(TX_MFB_DATA'length/8 -1 downto 0);

    signal meta_pattern_match_cntr_incr    : std_logic;
    signal meta_pattern_mismatch_cntr_incr : std_logic;

    signal pkt_size_16b : unsigned(15 downto 0);
    signal size_hash_16b : unsigned(15 downto 0);
    signal size_hash_8b : std_logic_vector(7 downto 0);

    -- =============================================================================================
    -- MFB Generator
    -- =============================================================================================
    signal gen_mfb_data    : std_logic_vector(TX_MFB_DATA'range);
    signal gen_mfb_meta    : std_logic_vector(log2(CHANNELS) + log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal gen_mfb_sof     : std_logic_vector(TX_MFB_SOF'range);
    signal gen_mfb_eof     : std_logic_vector(TX_MFB_EOF'range);
    signal gen_mfb_sof_pos : std_logic_vector(TX_MFB_SOF_POS'range);
    signal gen_mfb_eof_pos : std_logic_vector(TX_MFB_EOF_POS'range);
    signal gen_mfb_src_rdy : std_logic;
    signal gen_mfb_dst_rdy : std_logic;

    -- =============================================================================================
    -- Debug signals
    -- =============================================================================================
    attribute mark_debug : string;

    signal aux_sig_mfb_meta_chan_int                  : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal aux_sig_mfb_meta_pkt_size                  : std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal aux_sig_mfb_meta_hdr_meta                  : std_logic_vector(DMA_META_WIDTH -1 downto 0);

    signal tx_mfb_meta_chan_int                  : std_logic_vector(log2(CHANNELS) -1 downto 0);
    signal tx_mfb_meta_pkt_size                  : std_logic_vector(log2(PKT_SIZE_MAX+1) -1 downto 0);
    signal tx_mfb_meta_hdr_meta                  : std_logic_vector(DMA_META_WIDTH -1 downto 0);
    attribute mark_debug of tx_mfb_meta_chan_int : signal is "true";
    attribute mark_debug of tx_mfb_meta_pkt_size : signal is "true";
    attribute mark_debug of tx_mfb_meta_hdr_meta : signal is "true";
    attribute mark_debug of TX_MFB_DATA    : signal is "true";
    attribute mark_debug of TX_MFB_META    : signal is "true";
    attribute mark_debug of TX_MFB_SOF     : signal is "true";
    attribute mark_debug of TX_MFB_EOF     : signal is "true";
    attribute mark_debug of TX_MFB_SOF_POS : signal is "true";
    attribute mark_debug of TX_MFB_EOF_POS : signal is "true";
    attribute mark_debug of TX_MFB_SRC_RDY : signal is "true";
    attribute mark_debug of TX_MFB_DST_RDY : signal is "true";

    attribute mark_debug of pattern_comp_pst          : signal is "true";
    attribute mark_debug of pattern_match_cntr_incr  : signal is "true";
    attribute mark_debug of pattern_mismatch_cntr_incr  : signal is "true";
    attribute mark_debug of pattern_copy_val  : signal is "true";
    attribute mark_debug of meta_pattern_comp_pst          : signal is "true";
    attribute mark_debug of meta_pattern_match_cntr_incr  : signal is "true";
    attribute mark_debug of meta_pattern_mismatch_cntr_incr  : signal is "true";
    attribute mark_debug of meta_pattern_copy_val  : signal is "true";
begin

    tx_mfb_meta_chan_int     <= TX_MFB_META(log2(CHANNELS) -1 downto 0);
    tx_mfb_meta_hdr_meta     <= TX_MFB_META(log2(CHANNELS) + DMA_META_WIDTH-1 downto log2(CHANNELS));
    tx_mfb_meta_pkt_size     <= TX_MFB_META(log2(PKT_SIZE_MAX+1) + log2(CHANNELS) + DMA_META_WIDTH-1 downto log2(CHANNELS) + DMA_META_WIDTH);

    assert (MI_WIDTH=32)
        report "ERROR: TX DMA Debug core: MI_WIDTH ("&to_string(MI_WIDTH)&") must be 32b!"
        severity failure;

    mi_async_g: if (not MI_SAME_CLK) generate
        mi_async_i : entity work.MI_ASYNC
            generic map(
                DEVICE => DEVICE
                )
            port map(
                -- Master interface
                CLK_M     => MI_CLK,
                RESET_M   => MI_RESET,

                MI_M_DWR  => MI_DWR,
                MI_M_ADDR => MI_ADDR,
                MI_M_RD   => MI_RD,
                MI_M_WR   => MI_WR,
                MI_M_BE   => MI_BE,
                MI_M_DRD  => MI_DRD,
                MI_M_ARDY => MI_ARDY,
                MI_M_DRDY => MI_DRDY,

                -- Slave interface
                CLK_S     => CLK,
                RESET_S   => RESET,

                MI_S_DWR  => mi_sync_dwr,
                MI_S_ADDR => mi_sync_addr,
                MI_S_RD   => mi_sync_rd,
                MI_S_WR   => mi_sync_wr,
                MI_S_BE   => mi_sync_be,
                MI_S_DRD  => mi_sync_drd,
                MI_S_ARDY => mi_sync_ardy,
                MI_S_DRDY => mi_sync_drdy
                );
    else generate
        mi_sync_dwr  <= MI_DWR;
        mi_sync_addr <= MI_ADDR;
        mi_sync_rd   <= MI_RD;
        mi_sync_wr   <= MI_WR;
        mi_sync_be   <= MI_BE;
        MI_DRD       <= mi_sync_drd;
        MI_ARDY      <= mi_sync_ardy;
        MI_DRDY      <= mi_sync_drdy;
    end generate;

    mi_gen_spl_i : entity work.MI_SPLITTER_PLUS_GEN
        generic map(
            ADDR_WIDTH   => MI_WIDTH,
            DATA_WIDTH   => MI_WIDTH,
            META_WIDTH   => 0,
            PORTS        => MI_SPLIT_PORTS,
            PIPE_OUT     => (others => TRUE),
            PIPE_TYPE    => "SHREG",
            PIPE_OUTREG  => TRUE,

            ADDR_BASES  => MI_SPLIT_PORTS,
            ADDR_MASK   => MI_SPLIT_ADDR_MASK,
            ADDR_BASE   => MI_SPLIT_BASES,

            DEVICE       => DEVICE
            )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_DWR  => mi_sync_dwr,
            RX_MWR  => (others => '0'),
            RX_ADDR => mi_sync_addr,
            RX_BE   => mi_sync_be,
            RX_RD   => mi_sync_rd,
            RX_WR   => mi_sync_wr,
            RX_ARDY => mi_sync_ardy,
            RX_DRD  => mi_sync_drd,
            RX_DRDY => mi_sync_drdy,

            TX_DWR  => mi_split_dwr,
            TX_MWR  => open,
            TX_ADDR => mi_split_addr,
            TX_BE   => mi_split_be,
            TX_RD   => mi_split_rd,
            TX_WR   => mi_split_wr,
            TX_ARDY => mi_split_ardy,
            TX_DRD  => mi_split_drd,
            TX_DRDY => mi_split_drdy);

    -- =====================================================================
    --  MI reading interface
    -- =====================================================================
    -- Extract part of MI address which determines destination DMA Channel
    -- the destination DMA channel is specified within bits with the highest order
    mi_chan      <= mi_split_addr(0)(REG_ADDR_WIDTH+log2(CHANNELS)-1 downto REG_ADDR_WIDTH);
    mi_chanI     <= to_integer(unsigned(mi_chan));
    -- Extract part of MI address which determines destination register
    mi_reg_addr  <= mi_split_addr(0)(REG_ADDR_WIDTH-1 downto 0);
    mi_reg_addrI <= to_integer(unsigned(mi_reg_addr));

    mi_chan_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            mi_chan_reg <= mi_chan;
        end if;
    end process;

    -- MI read
    mi_rd_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            mi_split_drd(0) <= (others => '0');

            if (RESET='1') then
                mi_split_drdy(0) <= '0';
            else

                for i in 0 to REGS-1 loop
                    if (mi_reg_addrI=R_ADDRS(i)) then
                        mi_split_drd(0) <= (others => '0');
                        for e in 0 to MI_WIDTH/8-1 loop
                            if (mi_split_be(0)(e)='1') then
                                -- preparing data to read in every time
                                -- mi_split_BE in specified byte euqals 1
                                mi_split_drd(0)((e+1)*8-1 downto e*8) <= reg_dob_opt(i)(0)((e+1)*8-1 downto e*8);
                            end if;
                        end loop;
                    end if;
                end loop;

                mi_split_drdy(0) <= mi_split_rd(0);

            end if;
        end if;
    end process;

    mi_split_ardy(0) <= mi_split_rd(0) or mi_split_wr(0);
    -- =====================================================================


    -- =====================================================================
    -- Generation of storage for register values
    -- =====================================================================
    reg_gen : for i in 0 to REGS-1 generate
        -- Generate just one NP_LUTRAM for each MI transaction
        reg_i : entity work.NP_LUTRAM
            generic map(
                DATA_WIDTH  => MI_WIDTH,
                ITEMS       => CHANNELS,
                WRITE_PORTS => WR_PORTS(i),
                READ_PORTS  => RD_PORTS(i),
                DEVICE      => DEVICE
                )
            port map(
                WCLK  => CLK,
                DI    => reg_di (i)(WR_PORTS(i)-1 downto 0),
                WE    => reg_we (i)(WR_PORTS(i)-1 downto 0),
                ADDRA => reg_addra(i)(WR_PORTS(i)-1 downto 0),
                ADDRB => reg_addrb(i)(RD_PORTS(i)-1 downto 0),
                DOB   => reg_dob (i)(RD_PORTS(i)-1 downto 0)
                );

        strobe_gen : if (STROBE_EN(i)) generate

            -- Reset registers by writing 0
            -- Sample registers from counters by writing 1
            -- Reset and sample old value at the same time by writing 2
            with unsigned(mi_split_dwr_reg) select reg_di (i)(0) <=
                (others => '0') when to_unsigned(0, MI_WIDTH),
                cntr_do(i)      when others;

            -- reading is performed one clock cycle earlier than the writing
            reg_we (i)(0)   <= '1' when cntr_rd_reg = '1' or cntr_rst_reg = '1' else '0';
            reg_addra(i)(0) <= mi_chan_reg;
            reg_addrb(i)(0) <= mi_chan;

        else generate

            wr_en_gen : if (WR_EN(i)) generate
                -- Connect MI to the 0th write port of the register
                reg_di (i)(0) <= mi_split_dwr(0);
                reg_we (i)(0)   <= '1' when (mi_split_wr(0) = '1' and mi_reg_addrI = R_ADDRS(i)) else '0';
                reg_addra(i)(0) <= mi_chan;

            end generate;

            -- Connect MI to the 0th read port of the register (reading MI operations)
            reg_addrb(i)(0) <= mi_chan;
        end generate;

        -- Only connect valid output bits
        -- Set others to '0' to enable LUTmem optimalization
        reg_dob_opt_gen : for e in 0 to RD_PORTS(i)-1 generate
            reg_dob_opt(i)(e)(RD_WIDTH(i)-1 downto 0) <= reg_dob(i)(e)(RD_WIDTH(i)-1 downto 0);
        end generate;
    end generate;

    -- =====================================================================
    --  Counters logic
    -- =====================================================================

    dbg_cntrs_g   : for j in 0 to (CNT_NUM -1) generate
        dbg_cnt_i : entity work.CNT_MULTI_MEMX
            generic map(
                DEVICE        => DEVICE,
                CHANNELS      => CHANNELS,
                CNT_WIDTH     => DBG_CNTRS_WIDTH,
                INC_WIDTH     => 1,
                INC_FIFO_SIZE => 512
                )
            port map(
                CLK           => CLK,
                RESET         => RESET,

                INC_CH  => cntr_incr_chan(j),
                INC_VAL => (others => '1'),
                INC_VLD => cntr_incr_vld(j),
                INC_RDY => open,  -- If it overflows, it overflows

                RST_CH  => mi_chan,
                RST_VLD => cntr_rst,

                RD_CH  => mi_chan,
                RD_VLD => cntr_rd,
                RD_VAL => cntr_rd_val(j)
                );
    end generate;

    -- Reset when writing value 0 or 2 to any of the Strobing registers
    cntr_rst <= '1' when (mi_split_wr(0) = '1' and isStrobeAddr(mi_reg_addrI) and (unsigned(mi_split_dwr(0)) = 0 or unsigned(mi_split_dwr(0)) = 2 or unsigned(mi_split_dwr(0)) = 4)) else '0';
    -- Read when writing value 1 or 2 to any of the Strobing registers
    cntr_rd <= '1' when (mi_split_wr(0) = '1' and isStrobeAddr(mi_reg_addrI) and (unsigned(mi_split_dwr(0)) = 1 or unsigned(mi_split_dwr(0)) = 2)) else '0';

    cntr_rstrd_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            -- when the value 2 is written to the strobing register, than the
            -- reading operation from the register needs to be performed
            -- earlier than the writing operation, necessary delay is provided
            -- by the registers below
            cntr_rst_reg     <= cntr_rst;
            cntr_rd_reg      <= cntr_rd;
            mi_split_dwr_reg <= mi_split_dwr(0);
        end if;
    end process;

    -- Propagate counter values with correct signal width
    cntr_do_pr : process (all)
    begin
        cntr_do <= (others => (others => '0'));

        cntr_do(R_CNT_CORR_PKT_LENGTHS_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_CORR_PKT_LENGTHS_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_CORR_PKT_LENGTHS_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_CORR_PKT_LENGTHS_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_BAD_PKT_LENGTHS_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_BAD_PKT_LENGTHS_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_BAD_PKT_LENGTHS_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_BAD_PKT_LENGTHS_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_FR_LEN_OVF_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_FR_LEN_OVF_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_FR_LEN_OVF_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_FR_LEN_OVF_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_HDR_OUT_ORD_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_HDR_OUT_ORD_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_HDR_OUT_ORD_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_HDR_OUT_ORD_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_DMA_HDR_NUM_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_DMA_HDR_NUM_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_DMA_HDR_NUM_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_DMA_HDR_NUM_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_PCIE_LNG_CORR_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_PCIE_LNG_CORR_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_PCIE_LNG_CORR_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_PCIE_LNG_CORR_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_PCIE_LNG_INCORR_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_PCIE_LNG_INCORR_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_PCIE_LNG_INCORR_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_PCIE_LNG_INCORR_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_PTRN_MATCH_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_PTRN_MATCH_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_PTRN_MATCH_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_PTRN_MATCH_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_PTRN_MISMATCH_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_PTRN_MISMATCH_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_PTRN_MISMATCH_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_PTRN_MISMATCH_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_META_PTRN_MATCH_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_META_PTRN_MATCH_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_META_PTRN_MATCH_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_META_PTRN_MATCH_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;

        cntr_do(R_CNT_META_PTRN_MISMATCH_L) <= std_logic_vector(resize_left(unsigned(cntr_rd_val(R_CNT_META_PTRN_MISMATCH_L/2)), MI_WIDTH));
        if (DBG_CNTRS_WIDTH > MI_WIDTH) then
            cntr_do(R_CNT_META_PTRN_MISMATCH_H) <= std_logic_vector(resize_left(enlarge_right(unsigned(cntr_rd_val(R_CNT_META_PTRN_MISMATCH_L/2)), -MI_WIDTH), MI_WIDTH));
        end if;
    end process;

    -- =================================================================================================
    -- =============================================================================================
    -- Triggers of counter events
    -- =================================================================================================
    -- =============================================================================================

    -- =============================================================================================
    -- Frame length checking
    -- =============================================================================================
    mfb_frame_length_check_i : entity work.MFB_FRAME_LNG
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,
            META_WIDTH  => log2(PKT_SIZE_MAX+1) + DMA_META_WIDTH + log2(CHANNELS),

            LNG_WIDTH      => log2(PKT_SIZE_MAX+1),
            REG_BITMAP     => "111",
            SATURATION     => TRUE,
            IMPLEMENTATION => "parallel")
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_DATA    => RX_MFB_DATA,
            RX_META    => RX_MFB_META_PKT_SIZE & RX_MFB_META_HDR_META & RX_MFB_META_CHAN,
            RX_SOF_POS => RX_MFB_SOF_POS,
            RX_EOF_POS => RX_MFB_EOF_POS,
            RX_SOF     => RX_MFB_SOF,
            RX_EOF     => RX_MFB_EOF,
            RX_SRC_RDY => RX_MFB_SRC_RDY,
            RX_DST_RDY => RX_MFB_DST_RDY,

            TX_DATA    => fr_lng_mfb_data,
            TX_META    => fr_lng_mfb_meta,
            TX_SOF_POS => fr_lng_mfb_sof_pos,
            TX_EOF_POS => fr_lng_mfb_eof_pos,
            TX_SOF     => fr_lng_mfb_sof,
            TX_EOF     => fr_lng_mfb_eof,

            TX_COF       => open,
            TX_TEMP_LNG  => open,
            TX_FRAME_LNG => frame_chck_len,
            TX_FRAME_OVF => frame_chck_len_ovf,

            TX_SRC_RDY => fr_lng_mfb_src_rdy,
            TX_DST_RDY => fr_lng_mfb_dst_rdy);

    frame_len_storage_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                frame_len_stored  <= (others => '0');
                frame_chan_stored <= (others => '0');
            elsif (fr_lng_mfb_dst_rdy = '1') then
                frame_len_stored  <= frame_len_curr;
                frame_chan_stored <= frame_chan_curr;
            end if;
        end if;
    end process;

    frame_len_storage_nst_p : process (all) is
    begin
        frame_len_curr  <= frame_len_stored;
        frame_chan_curr <= frame_chan_stored;

        if (fr_lng_mfb_src_rdy = '1' and fr_lng_mfb_sof = "1") then
            frame_len_curr  <= unsigned(fr_lng_mfb_meta(log2(PKT_SIZE_MAX+1) + log2(CHANNELS) + DMA_META_WIDTH-1 downto log2(CHANNELS) + DMA_META_WIDTH));
            frame_chan_curr <= fr_lng_mfb_meta(log2(CHANNELS) -1 downto 0);
        end if;
    end process;

    frame_len_compare_p : process (all) is
    begin
        cntr_incr_chan(R_CNT_CORR_PKT_LENGTHS_L/2) <= (others => '0');
        cntr_incr_vld(R_CNT_CORR_PKT_LENGTHS_L/2)  <= '0';
        cntr_incr_chan(R_CNT_BAD_PKT_LENGTHS_L/2)  <= (others => '0');
        cntr_incr_vld(R_CNT_BAD_PKT_LENGTHS_L/2)   <= '0';

        if (fr_lng_mfb_src_rdy = '1' and fr_lng_mfb_dst_rdy = '1' and fr_lng_mfb_sof = "1" and fr_lng_mfb_eof = "1") then
            -- Count only when one packet begins and ends in a current word. Do not count situations
            -- when there are two packets in a single word, where one ends and another begins.
            if (unsigned(fr_lng_mfb_sof_pos) <= unsigned(fr_lng_mfb_eof_pos(fr_lng_mfb_eof_pos'high downto (fr_lng_mfb_eof_pos'high - fr_lng_mfb_sof_pos'length) + 1))) then
                if (frame_chck_len = fr_lng_mfb_meta(log2(PKT_SIZE_MAX+1) + log2(CHANNELS) + DMA_META_WIDTH -1 downto log2(CHANNELS) + DMA_META_WIDTH)) then
                    cntr_incr_chan(R_CNT_CORR_PKT_LENGTHS_L/2) <= fr_lng_mfb_meta(log2(CHANNELS) -1 downto 0);
                    cntr_incr_vld(R_CNT_CORR_PKT_LENGTHS_L/2)  <= '1';
                else
                    cntr_incr_chan(R_CNT_BAD_PKT_LENGTHS_L/2) <= fr_lng_mfb_meta(log2(CHANNELS) -1 downto 0);
                    cntr_incr_vld(R_CNT_BAD_PKT_LENGTHS_L/2)  <= '1';
                end if;
            else
                if (unsigned(frame_chck_len) = frame_len_stored) then
                    cntr_incr_chan(R_CNT_CORR_PKT_LENGTHS_L/2) <= frame_chan_stored;
                    cntr_incr_vld(R_CNT_CORR_PKT_LENGTHS_L/2)  <= '1';
                else
                    cntr_incr_chan(R_CNT_BAD_PKT_LENGTHS_L/2) <= frame_chan_stored;
                    cntr_incr_vld(R_CNT_BAD_PKT_LENGTHS_L/2)  <= '1';
                end if;
            end if;

        elsif (fr_lng_mfb_src_rdy = '1' and fr_lng_mfb_dst_rdy = '1' and fr_lng_mfb_sof = "0" and fr_lng_mfb_eof = "1") then
            if (unsigned(frame_chck_len) = frame_len_stored) then
                cntr_incr_chan(R_CNT_CORR_PKT_LENGTHS_L/2) <= frame_chan_stored;
                cntr_incr_vld(R_CNT_CORR_PKT_LENGTHS_L/2)  <= '1';
            else
                cntr_incr_chan(R_CNT_BAD_PKT_LENGTHS_L/2) <= frame_chan_stored;
                cntr_incr_vld(R_CNT_BAD_PKT_LENGTHS_L/2)  <= '1';
            end if;

        end if;
    end process;

    frame_len_ovf_cnt_incr_p : process (all) is
    begin

        cntr_incr_chan(R_CNT_FR_LEN_OVF_L/2) <= (others => '0');
        cntr_incr_vld(R_CNT_FR_LEN_OVF_L/2)  <= '0';

        if (fr_lng_mfb_src_rdy = '1' and fr_lng_mfb_dst_rdy = '1' and fr_lng_mfb_sof = "1" and fr_lng_mfb_eof = "1") then
            if (unsigned(fr_lng_mfb_sof_pos) <= unsigned(fr_lng_mfb_eof_pos(fr_lng_mfb_eof_pos'high downto (fr_lng_mfb_eof_pos'high - fr_lng_mfb_sof_pos'length) + 1))) then
                cntr_incr_chan(R_CNT_FR_LEN_OVF_L/2) <= fr_lng_mfb_meta(log2(CHANNELS) -1 downto 0);
                cntr_incr_vld(R_CNT_FR_LEN_OVF_L/2)  <= frame_chck_len_ovf(0);

            -- This should never occur as the start of frame is always aligned to the beginning of
            -- the region.
            else
                cntr_incr_chan(R_CNT_FR_LEN_OVF_L/2) <= frame_chan_stored;
                cntr_incr_vld(R_CNT_FR_LEN_OVF_L/2)  <= frame_chck_len_ovf(0);
            end if;
        elsif (fr_lng_mfb_src_rdy = '1' and fr_lng_mfb_dst_rdy = '1' and fr_lng_mfb_sof = "0" and fr_lng_mfb_eof = "1") then
            cntr_incr_chan(R_CNT_FR_LEN_OVF_L/2) <= frame_chan_stored;
            cntr_incr_vld(R_CNT_FR_LEN_OVF_L/2)  <= frame_chck_len_ovf(0);
        end if;
    end process;

    cntr_incr_chan(R_CNT_HDR_OUT_ORD_L/2) <= ST_SP_DBG_CHAN;
    cntr_incr_vld(R_CNT_HDR_OUT_ORD_L/2)  <= ST_SP_DBG_META(0);

    cntr_incr_chan(R_CNT_DMA_HDR_NUM_L/2) <= ST_SP_DBG_CHAN;
    cntr_incr_vld(R_CNT_DMA_HDR_NUM_L/2)  <= ST_SP_DBG_META(1);

    cntr_incr_chan(R_CNT_PCIE_LNG_CORR_L/2) <= ST_SP_DBG_CHAN;
    cntr_incr_vld(R_CNT_PCIE_LNG_CORR_L/2)  <= ST_SP_DBG_META(2);

    cntr_incr_chan(R_CNT_PCIE_LNG_INCORR_L/2) <= ST_SP_DBG_CHAN;
    cntr_incr_vld(R_CNT_PCIE_LNG_INCORR_L/2)  <= ST_SP_DBG_META(3);

    -- =================================================================================================
    -- Packet data pattern comparator
    -- =================================================================================================
    mfb_aux_signals_i : entity work.MFB_AUXILIARY_SIGNALS
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,

            META_WIDTH => log2(PKT_SIZE_MAX+1) + DMA_META_WIDTH + log2(CHANNELS),

            REGION_AUX_EN => FALSE,
            BLOCK_AUX_EN  => FALSE,
            ITEM_AUX_EN   => TRUE)
        port map (
            CLK   => CLK,
            RESET => RESET,

            RX_DATA    => fr_lng_mfb_data,
            RX_META    => fr_lng_mfb_meta,
            RX_SOF_POS => fr_lng_mfb_sof_pos,
            RX_EOF_POS => fr_lng_mfb_eof_pos,
            RX_SOF     => fr_lng_mfb_sof,
            RX_EOF     => fr_lng_mfb_eof,
            RX_SRC_RDY => fr_lng_mfb_src_rdy,
            RX_DST_RDY => fr_lng_mfb_dst_rdy,

            TX_DATA    => aux_sig_mfb_data,
            TX_META    => aux_sig_mfb_meta,
            TX_SOF_POS => aux_sig_mfb_sof_pos,
            TX_EOF_POS => aux_sig_mfb_eof_pos,
            TX_SOF     => aux_sig_mfb_sof,
            TX_EOF     => aux_sig_mfb_eof,
            TX_SRC_RDY => aux_sig_mfb_src_rdy,
            TX_DST_RDY => aux_sig_mfb_dst_rdy,

            TX_REGION_SHARED => open,
            TX_REGION_VLD    => open,
            TX_BLOCK_VLD     => open,
            TX_ITEM_VLD      => aux_sig_mfb_item_vld);

    aux_sig_mfb_meta_chan_int     <= aux_sig_mfb_meta(log2(CHANNELS) -1 downto 0);
    aux_sig_mfb_meta_hdr_meta     <= aux_sig_mfb_meta(log2(CHANNELS) + DMA_META_WIDTH-1 downto log2(CHANNELS));
    aux_sig_mfb_meta_pkt_size     <= aux_sig_mfb_meta(log2(PKT_SIZE_MAX+1) + log2(CHANNELS) + DMA_META_WIDTH-1 downto log2(CHANNELS) + DMA_META_WIDTH);

    pattern_comp_state_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                pattern_comp_pst <= S_IDLE;
                comp_val_stored  <= (others => '0');
            elsif (aux_sig_mfb_dst_rdy = '1') then
                pattern_comp_pst <= pattern_comp_nst;
                comp_val_stored  <= comp_val_curr;
            end if;
        end if;
    end process;

    -- The comparison needs to be done by bytes because the packet can be ended with byte accuracy.
    comp_arr_g : for i in 0 to (aux_sig_mfb_data'length/8 -1) generate
        comp_res_imm(i) <= '1' when (pattern_copy_val(i*8 + 7 downto i*8) = aux_sig_mfb_data(i*8 + 7 downto i*8)) else '0';
        comp_res_reg(i) <= '1' when (comp_val_stored(i*8 + 7 downto i*8) = aux_sig_mfb_data(i*8 + 7 downto i*8))  else '0';
    end generate;

    -- Tells which comparison results are valid and keeps their value. The reason for validaton is
    -- because the comparators funcion also in part of a word, where no packet is located.
    comp_res_imm_vld <= comp_res_imm and aux_sig_mfb_item_vld;
    comp_res_reg_vld <= comp_res_reg and aux_sig_mfb_item_vld;

    -- Tells which bytes differ in the comparison vector
    comp_res_imm_diff <= comp_res_imm_vld xor aux_sig_mfb_item_vld;
    comp_res_reg_diff <= comp_res_reg_vld xor aux_sig_mfb_item_vld;

    -- This copies the pattern over whole word
    patter_copy_val_g : for i in 0 to (aux_sig_mfb_data'length/32 -1) generate
        pattern_copy_val(i*32 + 31 downto i*32) <= aux_sig_mfb_data(31 downto 0);
    end generate;

    pattern_comp_nst_logic_p : process (all) is
        variable comp_res_diff_v : std_logic;
    begin
        pattern_comp_nst <= pattern_comp_pst;
        comp_val_curr    <= comp_val_stored;

        pattern_match_cntr_incr    <= '0';
        pattern_mismatch_cntr_incr <= '0';

        case pattern_comp_pst is
            when S_IDLE =>
                if (aux_sig_mfb_src_rdy = '1' and aux_sig_mfb_sof = "1") then
                    comp_val_curr <= pattern_copy_val;

                    -- compare immediate comparator values
                    if (aux_sig_mfb_eof = "1") then
                        pattern_match_cntr_incr    <= (not (or comp_res_imm_diff)) and aux_sig_mfb_dst_rdy;
                        pattern_mismatch_cntr_incr <= (or comp_res_imm_diff) and aux_sig_mfb_dst_rdy;

                    -- move to another state because the rest of the packet needs to be compared too
                    else
                        pattern_comp_nst <= S_COMP_MIDDLE_PKT;
                    end if;
                end if;

            when S_COMP_MIDDLE_PKT =>

                pattern_match_cntr_incr    <= (not (or comp_res_reg_diff)) and aux_sig_mfb_dst_rdy;
                pattern_mismatch_cntr_incr <= (or comp_res_reg_diff) and aux_sig_mfb_dst_rdy;

                comp_res_diff_v            := (or comp_res_reg_diff);
                if (aux_sig_mfb_eof = "1" or comp_res_diff_v = '1') then
                    pattern_comp_nst <= S_IDLE;
                end if;
        end case;
    end process;

    cntr_incr_chan(R_CNT_PTRN_MATCH_L/2)    <= aux_sig_mfb_meta(log2(CHANNELS) -1 downto 0);
    cntr_incr_vld(R_CNT_PTRN_MATCH_L/2)     <= pattern_match_cntr_incr when aux_sig_mfb_eof = "1" else '0';
    cntr_incr_chan(R_CNT_PTRN_MISMATCH_L/2) <= aux_sig_mfb_meta(log2(CHANNELS) -1 downto 0);
    cntr_incr_vld(R_CNT_PTRN_MISMATCH_L/2)  <= pattern_mismatch_cntr_incr;

    -- =============================================================================================
    -- Header metadata packet pattern matching
    -- =============================================================================================
    meta_pattern_comp_state_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RESET = '1') then
                meta_pattern_comp_pst <= S_IDLE;
                meta_comp_val_stored  <= (others => '0');
            elsif (aux_sig_mfb_dst_rdy = '1') then
                meta_pattern_comp_pst <= meta_pattern_comp_nst;
                meta_comp_val_stored  <= meta_comp_val_curr;
            end if;
        end if;
    end process;

    -- The comparison needs to be done by bytes because the packet can be ended with byte accuracy.
    meta_comp_arr_g : for i in 0 to (aux_sig_mfb_data'length/8 -1) generate
        meta_comp_res_imm(i) <= '1' when (meta_pattern_copy_val(i*8 + 7 downto i*8) = aux_sig_mfb_data(i*8 + 7 downto i*8)) else '0';
        meta_comp_res_reg(i) <= '1' when (meta_comp_val_stored(i*8 + 7 downto i*8) = aux_sig_mfb_data(i*8 + 7 downto i*8))  else '0';
    end generate;

    -- Tells which comparison results are valid and keeps their value. The reason for validaton is
    -- because the comparators funcion also in part of a word, where no packet is located.
    meta_comp_res_imm_vld <= meta_comp_res_imm and aux_sig_mfb_item_vld;
    meta_comp_res_reg_vld <= meta_comp_res_reg and aux_sig_mfb_item_vld;

    -- Tells which bytes differ in the comparison vector
    meta_comp_res_imm_diff <= meta_comp_res_imm_vld xor aux_sig_mfb_item_vld;
    meta_comp_res_reg_diff <= meta_comp_res_reg_vld xor aux_sig_mfb_item_vld;

    pkt_size_16b <= resize(unsigned(aux_sig_mfb_meta_pkt_size),16);
    size_hash_16b <= ("00000000" & pkt_size_16b(15 downto 8)) + pkt_size_16b;
    size_hash_8b <= std_logic_vector(size_hash_16b(7 downto 0));

    -- This copies the pattern over whole word
    meta_patter_copy_val_g : for i in 0 to (aux_sig_mfb_data'length/32 -1) generate
        meta_pattern_copy_val(i*32 + 31 downto i*32) <= std_logic_vector(resize(unsigned(aux_sig_mfb_meta_hdr_meta), 24)) & size_hash_8b;
    end generate;

    meta_pattern_comp_nst_logic_p : process (all) is
        variable comp_res_diff_v : std_logic;
    begin
        meta_pattern_comp_nst <= meta_pattern_comp_pst;
        meta_comp_val_curr    <= meta_comp_val_stored;

        meta_pattern_match_cntr_incr    <= '0';
        meta_pattern_mismatch_cntr_incr <= '0';

        case meta_pattern_comp_pst is
            when S_IDLE =>
                if (aux_sig_mfb_src_rdy = '1' and aux_sig_mfb_sof = "1") then
                    meta_comp_val_curr <= meta_pattern_copy_val;

                    -- compare immediate comparator values
                    if (aux_sig_mfb_eof = "1") then
                        meta_pattern_match_cntr_incr    <= (not (or meta_comp_res_imm_diff)) and aux_sig_mfb_dst_rdy;
                        meta_pattern_mismatch_cntr_incr <= (or meta_comp_res_imm_diff) and aux_sig_mfb_dst_rdy;

                    -- move to another state because the rest of the packet needs to be compared too
                    else
                        meta_pattern_comp_nst <= S_COMP_MIDDLE_PKT;
                    end if;
                end if;

            when S_COMP_MIDDLE_PKT =>

                meta_pattern_match_cntr_incr    <= (not (or meta_comp_res_reg_diff)) and aux_sig_mfb_dst_rdy;
                meta_pattern_mismatch_cntr_incr <= (or meta_comp_res_reg_diff) and aux_sig_mfb_dst_rdy;

                comp_res_diff_v            := (or meta_comp_res_reg_diff);
                if (aux_sig_mfb_eof = "1" or comp_res_diff_v = '1') then
                    meta_pattern_comp_nst <= S_IDLE;
                end if;
        end case;
    end process;

    cntr_incr_chan(R_CNT_META_PTRN_MATCH_L/2)    <= aux_sig_mfb_meta(log2(CHANNELS) -1 downto 0);
    cntr_incr_vld(R_CNT_META_PTRN_MATCH_L/2)     <= meta_pattern_match_cntr_incr when aux_sig_mfb_eof = "1" else '0';
    cntr_incr_chan(R_CNT_META_PTRN_MISMATCH_L/2) <= aux_sig_mfb_meta(log2(CHANNELS) -1 downto 0);
    cntr_incr_vld(R_CNT_META_PTRN_MISMATCH_L/2)  <= meta_pattern_mismatch_cntr_incr;

    -- ==============================================================================================
    -- MFB Generator
    -- ==============================================================================================
    mfb_generator_i : entity work.MFB_GENERATOR_MI32
        generic map (
            REGIONS        => MFB_REGIONS,
            REGION_SIZE    => MFB_REGION_SIZE,
            BLOCK_SIZE     => MFB_BLOCK_SIZE,
            ITEM_WIDTH     => MFB_ITEM_WIDTH,

            LENGTH_WIDTH   => log2(PKT_SIZE_MAX+1),

            CHANNELS_WIDTH => log2(CHANNELS),
            PKT_CNT_WIDTH  => DBG_CNTRS_WIDTH,
            USE_PACP_ARCH  => TRUE,
            DEVICE         => DEVICE)
        port map (
            CLK            => CLK,
            RST            => RESET,

            MI_DWR         => mi_split_dwr(1),
            MI_ADDR        => mi_split_addr(1),
            MI_BE          => mi_split_be(1),
            MI_RD          => mi_split_rd(1),
            MI_WR          => mi_split_wr(1),
            MI_ARDY        => mi_split_ardy(1),
            MI_DRD         => mi_split_drd(1),
            MI_DRDY        => mi_split_drdy(1),

            TX_MFB_DATA    => gen_mfb_data,
            TX_MFB_META    => gen_mfb_meta,
            TX_MFB_SOF     => gen_mfb_sof,
            TX_MFB_EOF     => gen_mfb_eof,
            TX_MFB_SOF_POS => gen_mfb_sof_pos,
            TX_MFB_EOF_POS => gen_mfb_eof_pos,
            TX_MFB_SRC_RDY => gen_mfb_src_rdy,
            TX_MFB_DST_RDY => gen_mfb_dst_rdy);

    mfb_merger_simple_i : entity work.MFB_MERGER_SIMPLE
        generic map (
            REGIONS     => MFB_REGIONS,
            REGION_SIZE => MFB_REGION_SIZE,
            BLOCK_SIZE  => MFB_BLOCK_SIZE,
            ITEM_WIDTH  => MFB_ITEM_WIDTH,

            META_WIDTH  => log2(PKT_SIZE_MAX+1) + DMA_META_WIDTH + log2(CHANNELS),
            MASKING_EN  => TRUE,
            CNT_MAX     => 32)
        port map (
            CLK             => CLK,
            RST             => RESET,

            RX_MFB0_DATA    => aux_sig_mfb_data,
            RX_MFB0_META    => aux_sig_mfb_meta,
            RX_MFB0_SOF     => aux_sig_mfb_sof,
            RX_MFB0_SOF_POS => aux_sig_mfb_sof_pos,
            RX_MFB0_EOF     => aux_sig_mfb_eof,
            RX_MFB0_EOF_POS => aux_sig_mfb_eof_pos,
            RX_MFB0_SRC_RDY => aux_sig_mfb_src_rdy,
            RX_MFB0_DST_RDY => aux_sig_mfb_dst_rdy,

            RX_MFB1_DATA    => gen_mfb_data,
            RX_MFB1_META    => gen_mfb_meta(log2(PKT_SIZE_MAX+1) -1 downto 0) & (DMA_META_WIDTH -1 downto 0 => '0') & gen_mfb_meta(log2(CHANNELS)+log2(PKT_SIZE_MAX+1)-1 downto log2(PKT_SIZE_MAX+1)),
            RX_MFB1_SOF     => gen_mfb_sof,
            RX_MFB1_SOF_POS => gen_mfb_sof_pos,
            RX_MFB1_EOF     => gen_mfb_eof,
            RX_MFB1_EOF_POS => gen_mfb_eof_pos,
            RX_MFB1_SRC_RDY => gen_mfb_src_rdy,
            RX_MFB1_DST_RDY => gen_mfb_dst_rdy,

            TX_MFB_DATA     => TX_MFB_DATA,
            TX_MFB_META     => TX_MFB_META,
            TX_MFB_SOF      => TX_MFB_SOF,
            TX_MFB_SOF_POS  => TX_MFB_SOF_POS,
            TX_MFB_EOF      => TX_MFB_EOF,
            TX_MFB_EOF_POS  => TX_MFB_EOF_POS,
            TX_MFB_SRC_RDY  => TX_MFB_SRC_RDY,
            TX_MFB_DST_RDY  => TX_MFB_DST_RDY);
end architecture;
