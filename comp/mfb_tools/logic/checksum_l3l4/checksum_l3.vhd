-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_CHECKSUM_L3 is
    generic (
        -- Number of Regions within a data word, must be power of 2.
        MFB_REGIONS      : natural := 1;
        -- Region size (in Blocks).
        MFB_REGION_SIZE  : natural := 8;
        -- Block size (in Items).
        MFB_BLOCK_SIZE   : natural := 8;
        -- Item width (in bits), must be 8.
        MFB_ITEM_WIDTH   : natural := 8;
        -- Maximum size of a packet (in Items).
        PKT_MTU          : natural := 2**14;
        -- Width of L3 offset signal in bits.
        OFFSET_WIDTH     : natural := 7;
        -- Width of L3 length signal in bits.
        LENGTH_WIDTH     : natural := 12;
        -- FPGA device name.
        -- Options: ULTRASCALE, STRATIX10, AGILEX, ...
        DEVICE           : string := "AGILEX"
    );
    port (
        -- ========================================================================
        -- Clock and Reset
        -- ========================================================================

        CLK                 : in  std_logic;
        RESET               : in  std_logic;

        -- ========================================================================
        -- RX interface
        --
        -- #. Input packets (MFB),
        -- #. Additional MFB meta signals valid with SOF.
        -- ========================================================================

        RX_MFB_DATA         : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_MFB_EOF_POS      : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF          : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_MFB_SRC_RDY      : in  std_logic;
        RX_MFB_DST_RDY      : out std_logic;

        -- Original value of the L3 checksum, valid with SOF.
        RX_MFB_L3_CSUM_ORIG : in  std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- Enable L3 (IPv4) checksum calculation, valid with SOF.
        RX_MFB_L3_CSUM_EN   : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Offset of the L3 header (from SOF), valid with SOF.
        -- WARNING: The offset, in combination with the length, must not exceed the packet.
        RX_MFB_L3_OFFSET    : in  std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);
        -- Length of the L3 header (from SOF), valid with SOF.
        -- WARNING: The length must not be zero or exceed a packet.
        RX_MFB_L3_LENGTH    : in  std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);

        -- ========================================================================
        -- TX interface
        -- ========================================================================

        TX_MVB_CSUM         : out std_logic_vector(MFB_REGIONS*16-1 downto 0);
        TX_MVB_CSUM_OK      : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_CSUM_EN      : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_VLD          : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MVB_SRC_RDY      : out std_logic;
        TX_MVB_DST_RDY      : in  std_logic
    );
end entity;

architecture FULL of MFB_CHECKSUM_L3 is

    signal cc_mvb_csum_raw      : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal cc_mvb_csum_raw_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_orig     : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal cc_mvb_csum_orig_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_orbe_arr : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_xarr     : u_array_t       (MFB_REGIONS-1 downto 0)(17-1 downto 0);
    signal cc_mvb_csum_arr      : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_le_arr   : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_same     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_csum_ok       : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_csum_bypass   : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_vld           : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_src_rdy       : std_logic;
    signal cc_mvb_dst_rdy       : std_logic;

begin

    csum_calc_i : entity work.CHECKSUM_CALCULATOR
    generic map (
        MFB_REGIONS     => MFB_REGIONS,
        MFB_REGION_SIZE => MFB_REGION_SIZE,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH,
        MFB_META_WIDTH  => 16,
        PKT_MTU         => PKT_MTU,
        OFFSET_WIDTH    => OFFSET_WIDTH,
        LENGTH_WIDTH    => LENGTH_WIDTH,
        NETWORK_ORDER   => True,
        DEVICE          => DEVICE
    )
    port map (
        CLK             => CLK,
        RESET           => RESET,

        RX_MFB_DATA     => RX_MFB_DATA,
        RX_MFB_META     => RX_MFB_L3_CSUM_ORIG,
        RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
        RX_MFB_SOF      => RX_MFB_SOF,
        RX_MFB_EOF      => RX_MFB_EOF,
        RX_MFB_SRC_RDY  => RX_MFB_SRC_RDY,
        RX_MFB_DST_RDY  => RX_MFB_DST_RDY,

        RX_OFFSET       => RX_MFB_L3_OFFSET,
        RX_LENGTH       => RX_MFB_L3_LENGTH,
        RX_CHSUM_EN     => RX_MFB_L3_CSUM_EN,

        TX_MVB_DATA     => cc_mvb_csum_raw, -- negated in big endian
        TX_MVB_META     => cc_mvb_csum_orig,
        TX_CHSUM_BYPASS => cc_mvb_csum_bypass,
        TX_MVB_VLD      => cc_mvb_vld,
        TX_MVB_SRC_RDY  => cc_mvb_src_rdy,
        TX_MVB_DST_RDY  => cc_mvb_dst_rdy
    );

    cc_mvb_csum_raw_arr  <= slv_array_deser(cc_mvb_csum_raw, MFB_REGIONS);
    cc_mvb_csum_orig_arr <= slv_array_deser(cc_mvb_csum_orig, MFB_REGIONS);

    csum_g : for ii in 0 to MFB_REGIONS-1 generate
        -- The original checksum from the parser is in little-endian byte order
        -- (as read from the MFB bus). The raw checksum from CHECKSUM_CALCULATOR
        -- (NETWORK_ORDER=True) is in big-endian. Convert original to big-endian
        -- so both operands use the same byte order.
        cc_mvb_csum_orbe_arr(ii) <= cc_mvb_csum_orig_arr(ii)(7 downto 0) & cc_mvb_csum_orig_arr(ii)(15 downto 8);

        -- Check if the calculated checksum is correct (raw sum == 0 means the
        -- 1's complement sum of all 16-bit words including the checksum field
        -- equals 0xFFFF, i.e. the checksum is valid).
        cc_mvb_csum_ok(ii) <= '1' when (unsigned(cc_mvb_csum_raw_arr(ii)) = 0) else '0';

        -- Compute the new checksum:
        --   raw = ~(sum_without_csum + old_csum)     -- negated sum over data including old checksum field
        --   ~raw + ~old_csum = sum_without_csum      -- negate raw to recover the sum, then subtract old checksum
        --   result = ~(sum_without_csum)             -- negate to get the final checksum
        -- All operations in 1's complement big-endian with end-around carry.
        cc_mvb_csum_xarr(ii) <= resize(unsigned(not cc_mvb_csum_raw_arr(ii)), 17) + unsigned(not cc_mvb_csum_orbe_arr(ii));
        cc_mvb_csum_arr(ii)  <= std_logic_vector(not (cc_mvb_csum_xarr(ii)(16-1 downto 0) + cc_mvb_csum_xarr(ii)(16)));

        -- DEBUG: Comparison of calculated and original checksum values.
        cc_mvb_csum_same(ii) <= '1' when (cc_mvb_csum_arr(ii) = cc_mvb_csum_orbe_arr(ii)) else '0';

        -- Convert result back to little-endian for output.
        cc_mvb_csum_le_arr(ii) <= cc_mvb_csum_arr(ii)(7 downto 0) & cc_mvb_csum_arr(ii)(15 downto 8);
    end generate;

    cc_mvb_dst_rdy <= TX_MVB_DST_RDY;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_MVB_DST_RDY = '1') then
                TX_MVB_CSUM    <= slv_array_ser(cc_mvb_csum_le_arr);
                TX_MVB_CSUM_OK <= cc_mvb_csum_ok;
                TX_MVB_CSUM_EN <= not cc_mvb_csum_bypass;
                TX_MVB_VLD     <= cc_mvb_vld;
                TX_MVB_SRC_RDY <= cc_mvb_src_rdy;
            end if;

            if (RESET = '1') then
                TX_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
