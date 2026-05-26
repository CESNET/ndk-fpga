-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity MFB_CHECKSUM_L4 is
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
        -- Width of L4 offset signal in bits.
        OFFSET_WIDTH     : natural := 8;
        -- Width of L4 length signal in bits.
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

        -- Original value of the L4 checksum, valid with SOF.
        RX_MFB_L4_CSUM_ORIG : in  std_logic_vector(MFB_REGIONS*16-1 downto 0);
        -- Enable L4 (IPv4) checksum calculation, valid with SOF.
        RX_MFB_L4_CSUM_EN   : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        -- Offset of the L4 protocol (from SOF), valid with SOF.
        -- WARNING: The offset, in combination with the length, must not exceed the packet.
        RX_MFB_L4_OFFSET    : in  std_logic_vector(MFB_REGIONS*OFFSET_WIDTH-1 downto 0);
        -- Length of the L4 protocol (from SOF), valid with SOF.
        -- WARNING: The length must not be zero or exceed a packet.
        RX_MFB_L4_LENGTH    : in  std_logic_vector(MFB_REGIONS*LENGTH_WIDTH-1 downto 0);
        -- L4 protocol number (required for pseudo-header), valid with SOF.
        RX_MFB_L4_PROTOCOL  : in  std_logic_vector(MFB_REGIONS*8-1 downto 0);
        -- Source IP address (required for pseudo-header), valid with SOF.
        -- For IPv4, the upper 96 bits are set to zero.
        RX_MFB_IP_SRC_ADDR  : in  std_logic_vector(MFB_REGIONS*128-1 downto 0);
        -- Destination IP address (required for pseudo-header), valid with SOF.
        -- For IPv4, the upper 96 bits are set to zero.
        RX_MFB_IP_DST_ADDR  : in  std_logic_vector(MFB_REGIONS*128-1 downto 0);
        -- Indicates if the packet is IPv6 (required for pseudo-header), valid with SOF.
        RX_MFB_IP_VER6      : in  std_logic_vector(MFB_REGIONS-1 downto 0);

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

architecture FULL of MFB_CHECKSUM_L4 is

    signal rx_mfb_l4_length_arr   : slv_array_t(MFB_REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal rx_mfb_l4_protocol_arr : slv_array_t(MFB_REGIONS-1 downto 0)(8-1 downto 0);
    signal rx_mfb_ip_src_addr_arr : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal rx_mfb_ip_dst_addr_arr : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);

    signal rx_mfb_src_rdy_calc    : std_logic;
    signal rx_mfb_dst_rdy_calc    : std_logic;
    signal rx_mfb_src_rdy_phdr    : std_logic;
    signal rx_mfb_dst_rdy_phdr    : std_logic;

    signal r0_ph_l4_len           : u_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal r0_ph_l4_proto         : u_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal r0_ph_ip_src           : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal r0_ph_ip_dst           : slv_array_t(MFB_REGIONS-1 downto 0)(128-1 downto 0);
    signal r0_ph_vld              : std_logic_vector(MFB_REGIONS-1 downto 0);

    signal s1_ph_vector           : u_array_t(MFB_REGIONS-1 downto 0)(18*16-1 downto 0);
    signal s1_ph_vector_be        : u_array_t(MFB_REGIONS-1 downto 0)(18*16-1 downto 0);
    signal s1_ph_csum             : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);

    signal r1_ph_csum             : slv_array_t(MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal r1_ph_vld              : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal s1_ph_src_rdy          : std_logic;
    signal s1_ph_dst_rdy          : std_logic;

    signal cc_mvb_csum_raw        : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal cc_mvb_csum_raw_arr    : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_orig       : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal cc_mvb_csum_orig_arr   : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal cc_mvb_csum_bypass     : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_meta_arr        : slv_array_t     (MFB_REGIONS-1 downto 0)(33-1 downto 0);
    signal cc_mvb_vld             : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal cc_mvb_src_rdy         : std_logic;
    signal cc_mvb_dst_rdy         : std_logic;

    signal mrg_mvb_meta           : std_logic_vector(MFB_REGIONS*33-1 downto 0);
    signal mrg_mvb_meta_arr       : slv_array_t     (MFB_REGIONS-1 downto 0)(33-1 downto 0);
    signal mrg_mvb_ph_csum        : std_logic_vector(MFB_REGIONS*16-1 downto 0);
    signal mrg_mvb_ph_csum_arr    : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_raw_arr   : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_orig_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_orbe_arr  : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_xraw_arr  : u_array_t       (MFB_REGIONS-1 downto 0)(17-1 downto 0);
    signal mrg_mvb_csum_fraw_arr  : u_array_t       (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_xarr      : u_array_t       (MFB_REGIONS-1 downto 0)(18-1 downto 0);
    signal mrg_mvb_csum_farr      : u_array_t       (MFB_REGIONS-1 downto 0)(17-1 downto 0);
    signal mrg_mvb_csum_zarr      : u_array_t       (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_arr       : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_le_arr    : slv_array_t     (MFB_REGIONS-1 downto 0)(16-1 downto 0);
    signal mrg_mvb_csum_same      : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mrg_mvb_csum_ok        : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mrg_mvb_csum_bypass    : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mrg_mvb_vld            : std_logic_vector(MFB_REGIONS-1 downto 0);
    signal mrg_mvb_src_rdy        : std_logic;
    signal mrg_mvb_dst_rdy        : std_logic;

begin

    rx_mfb_l4_length_arr   <= slv_array_deser(RX_MFB_L4_LENGTH, MFB_REGIONS);
    rx_mfb_l4_protocol_arr <= slv_array_deser(RX_MFB_L4_PROTOCOL, MFB_REGIONS);
    rx_mfb_ip_src_addr_arr <= slv_array_deser(RX_MFB_IP_SRC_ADDR, MFB_REGIONS);
    rx_mfb_ip_dst_addr_arr <= slv_array_deser(RX_MFB_IP_DST_ADDR, MFB_REGIONS);

    RX_MFB_DST_RDY      <= rx_mfb_dst_rdy_calc and rx_mfb_dst_rdy_phdr;
    rx_mfb_src_rdy_calc <= RX_MFB_SRC_RDY and rx_mfb_dst_rdy_phdr;
    rx_mfb_src_rdy_phdr <= RX_MFB_SRC_RDY and rx_mfb_dst_rdy_calc;

    --------------------------------------------------------------------
    -- Input registers (r0) include IPv4-mapped IPv6 transform
    --------------------------------------------------------------------

    rx_mfb_dst_rdy_phdr <= s1_ph_dst_rdy;

    r0_g: for ii in 0 to MFB_REGIONS-1 generate
        process (CLK)
        begin
            if rising_edge(CLK) then
                if (s1_ph_dst_rdy = '1') then
                    r0_ph_l4_len(ii)   <= resize(unsigned(rx_mfb_l4_length_arr(ii)), 16);
                    r0_ph_l4_proto(ii) <= resize(unsigned(rx_mfb_l4_protocol_arr(ii)), 16);

                    if (RX_MFB_IP_VER6(ii) = '1') then
                        r0_ph_ip_src(ii) <= rx_mfb_ip_src_addr_arr(ii);
                        r0_ph_ip_dst(ii) <= rx_mfb_ip_dst_addr_arr(ii);
                    else
                        -- IPv4-mapped IPv6 transform: 0000...0000FFFFxxxx
                        r0_ph_ip_src(ii) <= X"00000000000000000000FFFF" & rx_mfb_ip_src_addr_arr(ii)(32-1 downto 0);
                        r0_ph_ip_dst(ii) <= X"00000000000000000000FFFF" & rx_mfb_ip_dst_addr_arr(ii)(32-1 downto 0);
                    end if;

                    r0_ph_vld(ii) <= RX_MFB_SOF(ii) and rx_mfb_src_rdy_phdr;
                end if;
                if (RESET = '1') then
                    r0_ph_vld(ii) <= '0';
                end if;
            end if;
        end process;
    end generate;

    --------------------------------------------------------------------
    -- 1's complement calculation of pseudoheader
    --------------------------------------------------------------------

    s1_g: for ii in 0 to MFB_REGIONS-1 generate
        s1_ph_vector(ii) <= unsigned(r0_ph_ip_src(ii)) & unsigned(r0_ph_ip_dst(ii)) & r0_ph_l4_len(ii) & r0_ph_l4_proto(ii);

        be_g: for bb in 0 to 18-1 generate
            -- flip bytes within each 16-bit word to match network
            -- byte order (big-endian) expected by checksum calculation
            s1_ph_vector_be(ii)((bb+1)*16-1 downto bb*16) <= s1_ph_vector(ii)(bb*16+8-1 downto bb*16) & s1_ph_vector(ii)((bb+1)*16-1 downto bb*16+8);
        end generate;

        process (all)
            variable sum : unsigned(31 downto 0);
            variable tmp : unsigned(16 downto 0);
        begin
            sum := (others => '0');

            -- Add all 16-bit words of the pseudoheader.
            for i in 0 to 18-1 loop
                sum := sum + s1_ph_vector_be(ii)((i+1)*16-1 downto i*16);
            end loop;

            -- Fold carry (end-around) and take 1's complement.
            tmp := ('0' & sum(31 downto 16)) + ('0' & sum(15 downto 0));
            tmp := ('0' & tmp(15 downto 0)) + tmp(16);

            s1_ph_csum(ii) <= std_logic_vector(not tmp(15 downto 0));
        end process;
    end generate;

    --------------------------------------------------------------------
    -- Next registers (r1) include pseudoheader checksum
    --------------------------------------------------------------------

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (s1_ph_dst_rdy = '1') then
                r1_ph_csum <= s1_ph_csum;
                r1_ph_vld  <= r0_ph_vld;
            end if;
            if (RESET = '1') then
                r1_ph_vld <= (others => '0');
            end if;
        end if;
    end process;

    s1_ph_src_rdy <= or r1_ph_vld;

    --------------------------------------------------------------------
    -- Checksum calculation of L4 protocol
    --------------------------------------------------------------------

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
        RX_MFB_META     => RX_MFB_L4_CSUM_ORIG,
        RX_MFB_SOF_POS  => RX_MFB_SOF_POS,
        RX_MFB_EOF_POS  => RX_MFB_EOF_POS,
        RX_MFB_SOF      => RX_MFB_SOF,
        RX_MFB_EOF      => RX_MFB_EOF,
        RX_MFB_SRC_RDY  => rx_mfb_src_rdy_calc,
        RX_MFB_DST_RDY  => rx_mfb_dst_rdy_calc,

        RX_OFFSET       => RX_MFB_L4_OFFSET,
        RX_LENGTH       => RX_MFB_L4_LENGTH,
        RX_CHSUM_EN     => RX_MFB_L4_CSUM_EN,

        TX_MVB_DATA     => cc_mvb_csum_raw, -- negated in big endian
        TX_MVB_META     => cc_mvb_csum_orig,
        TX_CHSUM_BYPASS => cc_mvb_csum_bypass,
        TX_MVB_VLD      => cc_mvb_vld,
        TX_MVB_SRC_RDY  => cc_mvb_src_rdy,
        TX_MVB_DST_RDY  => cc_mvb_dst_rdy
    );

    cc_mvb_csum_raw_arr  <= slv_array_deser(cc_mvb_csum_raw, MFB_REGIONS);
    cc_mvb_csum_orig_arr <= slv_array_deser(cc_mvb_csum_orig, MFB_REGIONS);

    cc_mvb_meta_g: for ii in 0 to MFB_REGIONS-1 generate
        cc_mvb_meta_arr(ii)(15 downto 0)  <= cc_mvb_csum_raw_arr(ii);
        cc_mvb_meta_arr(ii)(31 downto 16) <= cc_mvb_csum_orig_arr(ii);
        cc_mvb_meta_arr(ii)(32)           <= cc_mvb_csum_bypass(ii);
    end generate;

    --------------------------------------------------------------------
    -- MVB merger
    --------------------------------------------------------------------

    mvb_merge_i : entity work.MVB_MERGE_ITEMS
    generic map (
        RX0_ITEMS      => MFB_REGIONS,
        RX0_ITEM_WIDTH => 33, -- 16 bits for raw checksum + 16 bits for original checksum + 1 bit for bypass
        RX1_ITEMS      => MFB_REGIONS,
        RX1_ITEM_WIDTH => 16, -- 16 bits for pseudoheader checksum
        RX0_FIFO_EN    => False,
        FIFO_DEPTH     => 32,
        OUTPUT_REG     => True,
        DEVICE         => DEVICE
    )
    port map (
        CLK         => CLK,
        RESET       => RESET,

        RX0_DATA    => slv_array_ser(cc_mvb_meta_arr),
        RX0_VLD     => cc_mvb_vld,
        RX0_SRC_RDY => cc_mvb_src_rdy,
        RX0_DST_RDY => cc_mvb_dst_rdy,

        RX1_DATA    => slv_array_ser(r1_ph_csum),
        RX1_VLD     => r1_ph_vld,
        RX1_SRC_RDY => s1_ph_src_rdy,
        RX1_DST_RDY => s1_ph_dst_rdy,

        TX_DATA     => open,
        TX_DATA0    => mrg_mvb_meta,
        TX_DATA1    => mrg_mvb_ph_csum,
        TX_VLD      => mrg_mvb_vld,
        TX_SRC_RDY  => mrg_mvb_src_rdy,
        TX_DST_RDY  => mrg_mvb_dst_rdy
    );

    mrg_mvb_ph_csum_arr <= slv_array_deser(mrg_mvb_ph_csum, MFB_REGIONS);
    mrg_mvb_meta_arr    <= slv_array_deser(mrg_mvb_meta, MFB_REGIONS);

    mrg_mvb_meta_g: for ii in 0 to MFB_REGIONS-1 generate
        mrg_mvb_csum_raw_arr(ii)  <= mrg_mvb_meta_arr(ii)(15 downto 0);
        mrg_mvb_csum_orig_arr(ii) <= mrg_mvb_meta_arr(ii)(31 downto 16);
        mrg_mvb_csum_bypass(ii)   <= mrg_mvb_meta_arr(ii)(32);
    end generate;

    --------------------------------------------------------------------
    -- Final checksum calculation and output registers (TX_MVB)
    --------------------------------------------------------------------

    csum_g : for ii in 0 to MFB_REGIONS-1 generate
        -- The original checksum from the parser is in little-endian byte order.
        -- The raw checksum (CHECKSUM_CALCULATOR with NETWORK_ORDER=True) and the
        -- pseudoheader checksum are both in big-endian. Convert original to
        -- big-endian so all operands use the same byte order.
        mrg_mvb_csum_orbe_arr(ii) <= mrg_mvb_csum_orig_arr(ii)(7 downto 0) & mrg_mvb_csum_orig_arr(ii)(15 downto 8);

        -- Step 1: Add raw L4 checksum and pseudoheader checksum.
        --   raw = ~(sum_l4_data + old_csum)    -- negated sum over L4 data including old checksum field
        --   ph   = ~(sum_pseudoheader)         -- negated sum over pseudoheader (IPs, proto, length)
        mrg_mvb_csum_xraw_arr(ii) <= resize(unsigned(mrg_mvb_csum_raw_arr(ii)), 17) + unsigned(mrg_mvb_ph_csum_arr(ii));

        -- Step 2: End-around carry on the 17-bit sum, producing a 16-bit value.
        --   fraw = xraw[15:0] + xraw[16]       -- fold carry back
        mrg_mvb_csum_fraw_arr(ii) <= (mrg_mvb_csum_xraw_arr(ii)(16-1 downto 0) + mrg_mvb_csum_xraw_arr(ii)(16));

        -- Check validity: for a correct packet, fraw == 0xFFFF (all ones).
        mrg_mvb_csum_ok(ii) <= '1' when (unsigned(mrg_mvb_csum_fraw_arr(ii)) = X"FFFF") else '0';

        -- Step 3: Compute the new checksum.
        --   ~fraw + ~old_csum                  -- negate fraw to recover the sum, subtract old checksum
        --   = ~(~(sum_l4 + sum_ph + old_csum)) + ~old_csum
        --   = sum_l4 + sum_ph                  -- old_csum cancels out
        --   result = ~(sum_l4 + sum_ph)        -- final negate gives the new checksum
        -- Uses fraw (16-bit, already folded) so the 1's complement negation is correct.
        mrg_mvb_csum_xarr(ii) <= resize(unsigned(not mrg_mvb_csum_fraw_arr(ii)), 18) + unsigned(not mrg_mvb_csum_orbe_arr(ii));

        -- Step 4: End-around carry on the 18-bit sum.
        mrg_mvb_csum_farr(ii) <= resize(mrg_mvb_csum_xarr(ii)(16-1 downto 0), 17) + mrg_mvb_csum_xarr(ii)(17 downto 16);

        -- Step 5: Final end-around carry and 1's complement negation.
        mrg_mvb_csum_zarr(ii) <= not (mrg_mvb_csum_farr(ii)(16-1 downto 0) + mrg_mvb_csum_farr(ii)(16));

        -- Step 6: Convert +0 (0x0000) to -0 (0xFFFF) per RFC 1071.
        mrg_mvb_csum_arr(ii)  <= X"FFFF" when (mrg_mvb_csum_zarr(ii) = 0) else std_logic_vector(mrg_mvb_csum_zarr(ii));

        -- Convert result back to little-endian for output.
        mrg_mvb_csum_le_arr(ii) <= mrg_mvb_csum_arr(ii)(7 downto 0) & mrg_mvb_csum_arr(ii)(15 downto 8);

        -- DEBUG: Comparison of calculated and original checksum values.
        mrg_mvb_csum_same(ii) <= '1' when (mrg_mvb_csum_arr(ii) = mrg_mvb_csum_orbe_arr(ii)) else '0';
    end generate;

    mrg_mvb_dst_rdy <= TX_MVB_DST_RDY;

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (TX_MVB_DST_RDY = '1') then
                TX_MVB_CSUM    <= slv_array_ser(mrg_mvb_csum_le_arr);
                TX_MVB_CSUM_OK <= mrg_mvb_csum_ok;
                TX_MVB_CSUM_EN <= not mrg_mvb_csum_bypass;
                TX_MVB_VLD     <= mrg_mvb_vld;
                TX_MVB_SRC_RDY <= mrg_mvb_src_rdy;
            end if;

            if (RESET = '1') then
                TX_MVB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
