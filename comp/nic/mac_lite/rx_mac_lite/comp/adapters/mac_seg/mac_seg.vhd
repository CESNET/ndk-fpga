-- mac_seg.vhd:
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal   <cabal@cesnet.cz>
--            Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity RX_MAC_LITE_ADAPTER_MAC_SEG is
    generic(
        REGIONS     : natural := 2;
        REGION_SIZE : natural := 8;
        SEGMENTS    : natural := REGIONS*REGION_SIZE
    );
    port(
        -- =====================================================================
        -- CLOCK AND RESET
        -- =====================================================================

        CLK              : in  std_logic;
        RESET            : in  std_logic;

        -- =====================================================================
        -- INPUT MAC SEGMENTED INTERFACE (Intel F-Tile IP)
        -- =====================================================================

        IN_MAC_DATA      : in  std_logic_vector(SEGMENTS*64-1 downto 0);
        IN_MAC_INFRAME   : in  std_logic_vector(SEGMENTS-1 downto 0);
        IN_MAC_EOP_EMPTY : in  std_logic_vector(SEGMENTS*3-1 downto 0);
        IN_MAC_FCS_ERROR : in  std_logic_vector(SEGMENTS-1 downto 0);
        -- Ignored
        IN_MAC_ERROR     : in  std_logic_vector(SEGMENTS*2-1 downto 0);
        -- Ignored
        IN_MAC_STATUS    : in  std_logic_vector(SEGMENTS*3-1 downto 0);
        IN_MAC_VALID     : in  std_logic;

        -- =====================================================================
        -- OUTPUT MFB INTERFACE
        --
        -- (RX MAC LITE, allowed MFB configurations: REGIONS,REGION_SIZE,8,8
        -- =====================================================================

        OUT_MFB_DATA     : out std_logic_vector(REGIONS*REGION_SIZE*64-1 downto 0);
        OUT_MFB_SOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SOF_POS  : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        OUT_MFB_EOF      : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_EOF_POS  : out std_logic_vector(REGIONS*log2(REGION_SIZE*8)-1 downto 0);
        OUT_MFB_ERROR    : out std_logic_vector(REGIONS-1 downto 0);
        OUT_MFB_SRC_RDY  : out std_logic;
        OUT_LINK_UP      : out std_logic;

        -- =======================================================================================
        -- OUTPUT STATISTICS INTERFACE (about 2 clock cycles earlier than the word reaches output)
        -- =======================================================================================

        -- number of discarded packets in the current word
        OUT_DISCARDED_PKTS  : out std_logic_vector(log2(SEGMENTS/2)-1 downto 0);
        -- 2*SEGMENTS*8 = bytes of 2 words
        OUT_DISCARDED_BYTES : out std_logic_vector(max(6, log2(2*SEGMENTS*8))-1 downto 0)
    );
end entity;

architecture FULL of RX_MAC_LITE_ADAPTER_MAC_SEG is

    constant WORD_LNG_WIDTH : natural := log2(REGIONS*REGION_SIZE*8+1);
    constant LNG_WIDTH      : natural := max(WORD_LNG_WIDTH,8);

    signal in_mac_boundary           : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_mac_sop                : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_mac_eop                : std_logic_vector(SEGMENTS-1 downto 0);
    signal in_mac_pkt_cont           : std_logic_vector(SEGMENTS downto 0);
    signal in_mac_seg_vld            : std_logic_vector(SEGMENTS-1 downto 0);

    signal reg1_mac_data             : std_logic_vector(SEGMENTS*64-1 downto 0);
    signal reg1_mac_inframe          : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg1_mac_empty            : std_logic_vector(SEGMENTS*            3-1 downto 0);
    signal reg1_mac_empty_arr        : slv_array_t     (SEGMENTS-1 downto 0)(3-1 downto 0);
    signal reg1_mac_eop_pos          : std_logic_vector(SEGMENTS*            3-1 downto 0);
    signal reg1_mac_eop_pos_arr      : slv_array_t     (SEGMENTS-1 downto 0)(3-1 downto 0);
    signal reg1_mac_sop              : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg1_mac_eop              : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg1_mac_error            : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg1_mac_src_rdy          : std_logic;

    signal tx_mfb_lng_data           : std_logic_vector(SEGMENTS*64-1 downto 0);
    signal tx_mfb_lng_eop_pos        : std_logic_vector(SEGMENTS*            3-1 downto 0);
    signal tx_mfb_lng_sop            : std_logic_vector(SEGMENTS-1 downto 0);
    signal tx_mfb_lng_eop            : std_logic_vector(SEGMENTS-1 downto 0);
    signal tx_mfb_lng_error          : std_logic_vector(SEGMENTS-1 downto 0);
    signal tx_mfb_lng_src_rdy        : std_logic;

    signal tx_mfb_lng_mid_pkt_gap    : std_logic;
    signal tx_mfb_lng_cof            : std_logic_vector(SEGMENTS-1 downto 0);
    signal tx_mfb_lng_lenth          : std_logic_vector(SEGMENTS*            LNG_WIDTH-1 downto 0);
    signal tx_mfb_lng_lenth_arr      : slv_array_t     (SEGMENTS-1 downto 0)(LNG_WIDTH-1 downto 0);
    signal tx_mfb_lng_bytes_count    : u_array_t       (SEGMENTS-1 downto 0)(LNG_WIDTH-1 downto 0);
    signal tx_mfb_lng_undersized     : std_logic_vector(SEGMENTS-1 downto 0);

    signal reg2_mac_data             : std_logic_vector(SEGMENTS*64-1 downto 0);
    signal reg2_mac_sop              : std_logic_vector(SEGMENTS   -1 downto 0);
    signal reg2_mac_eop              : std_logic_vector(SEGMENTS   -1 downto 0);
    signal reg2_mac_eop_pos          : std_logic_vector(SEGMENTS* 3-1 downto 0);
    signal reg2_mac_error            : std_logic_vector(SEGMENTS   -1 downto 0);
    signal reg2_mac_valid            : std_logic;

    -- statistic signals
    signal discarded_pkts            : std_logic_vector(log2(SEGMENTS+1)-1 downto 0);
    signal discarded_bytes           : std_logic_vector(max(6, log2(2*SEGMENTS*8))-1 downto 0);

    signal reg2_undersized           : std_logic_vector(SEGMENTS-1 downto 0);
    signal first_pkt_undersized      : std_logic;
    signal reg2_mac_sop_masked       : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg2_mac_eop_masked       : std_logic_vector(SEGMENTS-1 downto 0);
    signal reg2_mac_valid_masked     : std_logic;

    signal sig1_mfb_sof              : std_logic_vector(REGIONS-1 downto 0);
    signal sig1_mfb_eof              : std_logic_vector(REGIONS-1 downto 0);
    signal sig1_mfb_sof_pos_arr      : slv_array_t     (REGIONS-1 downto 0)(max(1,log2(REGION_SIZE))-1 downto 0);
    signal sig1_mfb_eof_pos_hi_arr   : slv_array_t     (REGIONS-1 downto 0)(max(1,log2(REGION_SIZE))-1 downto 0);
    signal sig1_mfb_eof_pos_lo_arr   : slv_array_t     (REGIONS-1 downto 0)(3-1 downto 0);
    signal sig1_mfb_eof_pos_arr      : slv_array_t     (REGIONS-1 downto 0)(log2(REGION_SIZE*8)-1 downto 0);
    signal sig1_mfb_error            : std_logic_vector(REGIONS-1 downto 0);

    signal sig1_mfb_pkt_cont         : std_logic_vector(REGIONS+1-1 downto 0);
    signal sig1_mfb_vld              : std_logic_vector(REGIONS-1 downto 0);

begin

    mac_boundary_g : if (SEGMENTS=1) generate
        in_mac_boundary(0) <= reg1_mac_inframe(0) xor IN_MAC_INFRAME(0);
    else generate
        in_mac_boundary <= (IN_MAC_INFRAME(SEGMENTS-2 downto 0) & reg1_mac_inframe(SEGMENTS-1)) xor IN_MAC_INFRAME;
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (IN_MAC_VALID = '1') then
                reg1_mac_inframe <= IN_MAC_INFRAME;
            end if;
            if (RESET = '1') then
                reg1_mac_inframe <= (others => '0');
            end if;
        end if;
    end process;

    in_mac_sop <= IN_MAC_VALID and in_mac_boundary and     IN_MAC_INFRAME;
    in_mac_eop <= IN_MAC_VALID and in_mac_boundary and not IN_MAC_INFRAME;

    in_mac_pkt_cont_g : for s in 0 to SEGMENTS-1 generate
        in_mac_pkt_cont(s+1) <= (    in_mac_sop(s) and not in_mac_eop(s) and not in_mac_pkt_cont(s)) or
                                (    in_mac_sop(s) and     in_mac_eop(s) and     in_mac_pkt_cont(s)) or
                                (not in_mac_sop(s) and not in_mac_eop(s) and     in_mac_pkt_cont(s));

        in_mac_seg_vld(s) <= in_mac_sop(s) or in_mac_eop(s) or in_mac_pkt_cont(s);
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (IN_MAC_VALID = '1') then
                in_mac_pkt_cont(0) <= in_mac_pkt_cont(SEGMENTS);
            end if;
            if (RESET = '1') then
                in_mac_pkt_cont(0) <= '0';
            end if;
        end if;
    end process;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            reg1_mac_data      <= IN_MAC_DATA;
            reg1_mac_empty     <= IN_MAC_EOP_EMPTY;
            reg1_mac_sop       <= in_mac_sop;
            reg1_mac_eop       <= in_mac_eop;
            reg1_mac_error     <= IN_MAC_FCS_ERROR;
            reg1_mac_src_rdy   <= (or in_mac_seg_vld) and IN_MAC_VALID;
            if (RESET = '1') then
                reg1_mac_src_rdy <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Discard frames with length between 9 and 59 B
    -- ========================================================================

    reg1_mac_empty_arr <= slv_array_deser(reg1_mac_empty, SEGMENTS);
    reg1_mac_eop_pos_arr_g: for s in 0 to SEGMENTS-1 generate
        reg1_mac_eop_pos_arr(s) <= std_logic_vector(7 - unsigned(reg1_mac_empty_arr(s)));
    end generate;
    reg1_mac_eop_pos <= slv_array_ser(reg1_mac_eop_pos_arr);

    mfb_frame_lng_i : entity work.MFB_FRAME_LNG
    generic map (
        REGIONS        => SEGMENTS,
        REGION_SIZE    => 1,
        BLOCK_SIZE     => 8,
        ITEM_WIDTH     => 8,
        META_WIDTH     => 1,
        LNG_WIDTH      => LNG_WIDTH,
        REG_BITMAP     => "111",
        SATURATION     => True,
        IMPLEMENTATION => "parallel"
    )
    port map (
        CLK              => CLK  ,
        RESET            => RESET,

        RX_DATA          => reg1_mac_data   ,
        RX_META          => reg1_mac_error  ,
        RX_SOF_POS       => (others => '0') ,
        RX_EOF_POS       => reg1_mac_eop_pos,
        RX_SOF           => reg1_mac_sop    ,
        RX_EOF           => reg1_mac_eop    ,
        RX_SRC_RDY       => reg1_mac_src_rdy,
        RX_DST_RDY       => open            ,

        TX_DATA          => tx_mfb_lng_data   ,
        TX_META          => tx_mfb_lng_error  ,
        TX_SOF_POS       => open              ,
        TX_EOF_POS       => tx_mfb_lng_eop_pos,
        TX_SOF           => tx_mfb_lng_sop    ,
        TX_EOF           => tx_mfb_lng_eop    ,
        TX_SRC_RDY       => tx_mfb_lng_src_rdy,
        TX_DST_RDY       => '1',

        TX_COF           => tx_mfb_lng_cof,
        TX_TEMP_LNG      => open,
        TX_FRAME_LNG     => tx_mfb_lng_lenth
    );

    tx_mfb_lng_lenth_arr <= slv_array_deser(tx_mfb_lng_lenth, SEGMENTS);
    undersized_g : for s in 0 to SEGMENTS-1 generate
        tx_mfb_lng_bytes_count(s) <= unsigned(tx_mfb_lng_lenth_arr(s));
        tx_mfb_lng_undersized (s) <= '1' when ((tx_mfb_lng_bytes_count(s) < 60) and (tx_mfb_lng_eop(s) = '1')) else '0';
    end generate;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (tx_mfb_lng_src_rdy = '1') then
                reg2_undersized <= tx_mfb_lng_undersized;
            end if;
            if (RESET = '1') then
                reg2_undersized <= (others => '0');
            end if;
        end if;
    end process;

    tx_mfb_lng_mid_pkt_gap <= '1' when ((tx_mfb_lng_cof(0) = '1') and (tx_mfb_lng_src_rdy = '0')) else '0';
    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (tx_mfb_lng_mid_pkt_gap = '0') then
                reg2_mac_data      <= tx_mfb_lng_data;
                reg2_mac_eop_pos   <= tx_mfb_lng_eop_pos;
                reg2_mac_sop       <= tx_mfb_lng_sop;
                reg2_mac_eop       <= tx_mfb_lng_eop;
                reg2_mac_error     <= tx_mfb_lng_error;
                reg2_mac_valid     <= tx_mfb_lng_src_rdy;
            end if;
            if (RESET = '1') then
                reg2_mac_valid <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Discard statistics
    -- ========================================================================
    sum_one_i : entity work.SUM_ONE
    generic map (
        INPUT_WIDTH  => SEGMENTS,
        OUTPUT_WIDTH => log2(SEGMENTS+1),
        OUTPUT_REG   => false
    )
    port map (
        CLK      => CLK  ,
        RESET    => RESET,

        DIN      => tx_mfb_lng_undersized,
        DIN_MASK => (others => '1'),
        DIN_VLD  => '1'            ,

        DOUT     => discarded_pkts,
        DOUT_VLD => open
    );

    process(all)
        variable dis_bytes_count : unsigned(max(6, log2(2*SEGMENTS*8))-1 downto 0);
    begin
        dis_bytes_count := (others => '0');
        for s in 0 to SEGMENTS-1 loop
            if (tx_mfb_lng_undersized(s) = '1') then
                dis_bytes_count := dis_bytes_count + tx_mfb_lng_bytes_count(s)(6-1 downto 0);
            end if;
        end loop;
        discarded_bytes <= std_logic_vector(dis_bytes_count);
    end process;

    process(CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                OUT_DISCARDED_PKTS  <= (others => '0');
                OUT_DISCARDED_BYTES <= (others => '0');
            else
                OUT_DISCARDED_PKTS  <= discarded_pkts(log2(SEGMENTS/2)-1 downto 0);
                OUT_DISCARDED_BYTES <= discarded_bytes;
            end if;
        end if;
    end process;

    -- ========================================================================
    -- Mask undersized packets
    -- ========================================================================
    -- Is the first packet in the previous word (tx_mfb_lng_*) undersized?
    -- Then mask last SOP in the current word (reg2_mac_*)!
    process(all)
    begin
        first_pkt_undersized <= '0';
        for s in 0 to SEGMENTS-1 loop
            if (tx_mfb_lng_eop(s) = '1') then
                first_pkt_undersized <= tx_mfb_lng_undersized(s);
                exit;
            end if;
        end loop;
    end process;

    mask_sop_eop_p : process (all)
        variable mask_sop : std_logic;
    begin
        -- init
        reg2_mac_sop_masked <= reg2_mac_sop;
        reg2_mac_eop_masked <= reg2_mac_eop;
        mask_sop := '0';
        if ((tx_mfb_lng_cof(0) = '1') and (first_pkt_undersized = '1')) then
            mask_sop := '1';
        end if;
        -- mask
        for s in SEGMENTS-1 downto 0 loop
            -- mask the current EOP
            if (reg2_undersized(s) = '1') then
                reg2_mac_eop_masked(s) <= '0';
                mask_sop := '1';
            end if;
            -- mask the following SOP
            if ((mask_sop = '1') and (reg2_mac_sop(s) = '1')) then
                reg2_mac_sop_masked(s) <= '0';
                mask_sop := '0';
            end if;
        end loop;
    end process;

    -- invalidate word when there is a mid-packet gap
    reg2_mac_valid_masked <= reg2_mac_valid and not tx_mfb_lng_mid_pkt_gap;

    -- ========================================================================
    -- Convert to MFB
    -- ========================================================================
    one_segment_opt_g : if SEGMENTS>1 generate
        sig1_mfb_g : for i in 0 to REGIONS-1 generate
            sig1_mfb_sof(i) <= or reg2_mac_sop_masked((i+1)*REGION_SIZE-1 downto i*REGION_SIZE);
            sig1_mfb_eof(i) <= or reg2_mac_eop_masked((i+1)*REGION_SIZE-1 downto i*REGION_SIZE);

            sof_pos_enc_i : entity work.GEN_ENC
            generic map (
                ITEMS => REGION_SIZE
            )
            port map (
                DI   => reg2_mac_sop_masked((i+1)*REGION_SIZE-1 downto i*REGION_SIZE),
                ADDR => sig1_mfb_sof_pos_arr(i)
            );

            eof_pos_hi_enc_i : entity work.GEN_ENC
            generic map (
                ITEMS => REGION_SIZE
            )
            port map (
                DI   => reg2_mac_eop_masked((i+1)*REGION_SIZE-1 downto i*REGION_SIZE),
                ADDR => sig1_mfb_eof_pos_hi_arr(i)
            );

            eof_pos_lo_mux_i : entity work.GEN_MUX_ONEHOT
            generic map (
                DATA_WIDTH => 3,
                MUX_WIDTH  => REGION_SIZE
            )
            port map (
                DATA_IN  => reg2_mac_eop_pos   ((i+1)*(REGION_SIZE*3)-1 downto i*(REGION_SIZE*3)),
                SEL      => reg2_mac_eop_masked((i+1)* REGION_SIZE   -1 downto i* REGION_SIZE   ),
                DATA_OUT => sig1_mfb_eof_pos_lo_arr(i)
            );

            sig1_mfb_eof_pos_arr(i) <= sig1_mfb_eof_pos_hi_arr(i) & sig1_mfb_eof_pos_lo_arr(i);

            sig1_mfb_error(i) <= or (reg2_mac_eop_masked((i+1)*REGION_SIZE-1 downto i*REGION_SIZE) and
                                     reg2_mac_error     ((i+1)*REGION_SIZE-1 downto i*REGION_SIZE));
        end generate;
    else generate
        sig1_mfb_sof <= reg2_mac_sop_masked;
        sig1_mfb_eof <= reg2_mac_eop_masked;

        sig1_mfb_sof_pos_arr(0) <= (others => '0');
        sig1_mfb_eof_pos_arr(0) <= reg2_mac_eop_pos;

        sig1_mfb_error(0) <= or (reg2_mac_eop_masked and reg2_mac_error);
    end generate;

    sig1_mfb_pkt_cont_g : for r in 0 to REGIONS-1 generate
        sig1_mfb_pkt_cont(r+1) <= (    sig1_mfb_sof(r) and not sig1_mfb_eof(r) and not sig1_mfb_pkt_cont(r)) or
                                  (    sig1_mfb_sof(r) and     sig1_mfb_eof(r) and     sig1_mfb_pkt_cont(r)) or
                                  (not sig1_mfb_sof(r) and not sig1_mfb_eof(r) and     sig1_mfb_pkt_cont(r));

        sig1_mfb_vld(r) <= sig1_mfb_sof(r) or sig1_mfb_eof(r) or sig1_mfb_pkt_cont(r);
    end generate;

    process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (reg2_mac_valid_masked = '1') then
                sig1_mfb_pkt_cont(0) <= sig1_mfb_pkt_cont(REGIONS);
            end if;
            if (RESET = '1') then
                sig1_mfb_pkt_cont(0) <= '0';
            end if;
        end if;
    end process;

    mfb_reg_out_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            OUT_MFB_DATA    <= reg2_mac_data;
            OUT_MFB_SOF     <= sig1_mfb_sof;
            OUT_MFB_SOF_POS <= slv_array_ser(sig1_mfb_sof_pos_arr);
            OUT_MFB_EOF     <= sig1_mfb_eof;
            OUT_MFB_EOF_POS <= slv_array_ser(sig1_mfb_eof_pos_arr);
            OUT_MFB_ERROR   <= sig1_mfb_error;
            OUT_MFB_SRC_RDY <= (or sig1_mfb_vld) and reg2_mac_valid_masked;
            if (RESET = '1') then
                OUT_MFB_SRC_RDY <= '0';
            end if;
        end if;
    end process;

end architecture;
