-- mfb_generator_core_pacp.vhd: This component generates packets of desired length.
-- Copyright (C) 2020 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

----------------------------------------------------------------------------
-- Description
----------------------------------------------------------------------------
-- This is an alternative version of MFB Generator Core, which uses component
-- Packet Planner and thus has better timing.
----------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.type_pack.all;
use work.math_pack.all;

entity MFB_GENERATOR_CORE_PACP is
    Generic (
        -- number of regions in a data word
        REGIONS         : natural := 2;
        -- number of blocks in a region
        REGION_SIZE     : natural := 8;
        -- number of items in a block
        BLOCK_SIZE      : natural := 8;
        -- number of bits in an item
        ITEM_WIDTH      : natural := 8;
        -- the width of length signal
        LENGTH_WIDTH    : natural := 10;
        -- target device
        DEVICE          : string := "ULTRASCALE"
    );
    Port (
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        -- Generator control special dynamic interface
        -- =====================================================================
        -- At begin are values in all regions same, when is set ACCEPT in some
        -- region, then in next region must be new value (in same clock cycle).
        GEN_LENGTH     : in  slv_array_t(REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
        GEN_VALID      : in  std_logic_vector(REGIONS-1 downto 0);
        GEN_ACCEPT     : out std_logic_vector(REGIONS-1 downto 0);

        -- TX MFB interface without data
        -- =====================================================================
        TX_MFB_SOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_GENERATOR_CORE_PACP is

    constant BLOCK_WIDTH    : natural := ITEM_WIDTH*BLOCK_SIZE;
    constant REGION_WIDTH   : natural := BLOCK_WIDTH*REGION_SIZE;
    constant WORD_WIDTH     : natural := REGION_WIDTH*REGIONS;

    constant REGION_ITEMS   : natural := REGION_WIDTH/ITEM_WIDTH;
    constant WORD_ITEMS     : natural := WORD_WIDTH/ITEM_WIDTH;

    constant SPACE_SIZE     : natural := 2**(LENGTH_WIDTH+1);

    constant SPACE_WORDS    : natural := SPACE_SIZE/WORD_ITEMS;

    -- Generator is stopped
    signal is_stopped     : std_logic;

    -- Packet Planner input
    signal gen_afull      : std_logic;

    -- Packet Planner Read Pointer
    signal rd_ptr_reg     : unsigned(log2(SPACE_WORDS)-1 downto 0) := (others => '0');
    signal rd_ptr_dec     : unsigned(log2(SPACE_WORDS)-1 downto 0) := (others => '0');
    signal rd_ptr_used    : unsigned(log2(SPACE_WORDS)-1 downto 0) := (others => '0');
    signal rd_ptr         : std_logic_vector(log2(SPACE_SIZE)-log2(BLOCK_SIZE)-1 downto 0);
    signal wr_ptr         : std_logic_vector(log2(SPACE_SIZE)-log2(BLOCK_SIZE)-1 downto 0);

    -- Packet Planner output
    signal pkt_len        : slv_array_t     (REGIONS-1 downto 0)(LENGTH_WIDTH-1 downto 0);
    signal pkt_addr       : slv_array_t     (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal pkt_vld        : std_logic_vector(REGIONS-1 downto 0);
    signal pkt_dst_rdy    : std_logic_vector(REGIONS-1 downto 0);
    signal pkt_curr_word  : std_logic;

    signal pkt_sptr       : slv_array_t     (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal pkt_eptr       : slv_array_t     (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);

    -- Register 0
    signal reg0_ptr       : unsigned(log2(SPACE_WORDS)-1 downto 0);
    signal reg0_sptr      : slv_array_t     (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg0_eptr      : slv_array_t     (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg0_vld       : std_logic_vector(REGIONS-1 downto 0);

    signal reg0_prev_eptr : unsigned(log2(SPACE_SIZE)-1 downto 0);
    signal reg0_prev_vld  : std_logic;

    signal reg0_sptr_vec  : u_array_t       (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg0_svld_vec  : std_logic_vector(REGIONS-1 downto 0);
    signal reg0_eptr_vec  : u_array_t       (REGIONS+1-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg0_evld_vec  : std_logic_vector(REGIONS+1-1 downto 0);

    -- Register 1
    signal reg1_sptr      : u_array_t       (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg1_svld      : std_logic_vector(REGIONS-1 downto 0);
    signal reg1_eptr      : u_array_t       (REGIONS-1 downto 0)(log2(SPACE_SIZE)-1 downto 0);
    signal reg1_evld      : std_logic_vector(REGIONS-1 downto 0);

    -- SOF_POS and EOF_POS
    signal TX_MFB_SOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(max(1,log2(REGION_SIZE))-1 downto 0);
    signal TX_MFB_EOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);

    -- In frame detection register
    signal tx_mfb_inframe : std_logic;

begin

    is_stopped <= (nor GEN_VALID);

    ----------------------------------------------------------------------------
    -- Packet Planner
    ----------------------------------------------------------------------------

    packet_planner_i : entity work.PACKET_PLANNER
    generic map(
        DEVICE            => DEVICE               ,
        STREAMS           => 1                    ,
        PKTS              => REGIONS              ,
        PLANNED_PKTS      => REGIONS              ,
        METADATA_WIDTH    => 0                    ,
        SPACE_SIZE        => SPACE_SIZE           ,
        SPACE_WORD_SIZE   => WORD_WIDTH/ITEM_WIDTH,
        PKT_SIZE          => 2**(LENGTH_WIDTH-1)  ,
        GAP_SIZE          => 4                    ,
        GAP_SIZE_MIN      => 4                    ,
        ALIGN             => BLOCK_SIZE           ,
        FIFO_ITEMS        => 32                   ,
        FIFO_AFULL_OFFSET => 1                    ,
        STREAM_OUT_EN     => false                ,
        GLOBAL_OUT_EN     => true                 ,
        STREAM_OUT_AFULL  => false                ,
        GLOBAL_OUT_AFULL  => false
    )
    port map(
        CLK   => CLK  ,
        RESET => RESET,

        -- Vivado 2019.1
        --RX_STR_PKT_META   (0) => (others => (others => '0'))     ,
        -- Vivado 2022.1 and newer
        RX_STR_PKT_META       => (others => (others => (others => '0'))),
        RX_STR_PKT_LEN    (0) => GEN_LENGTH                      ,
        RX_STR_PKT_VLD    (0) => GEN_VALID                       ,
        RX_STR_PKT_SRC_RDY(0) => (or GEN_VALID) and not gen_afull,
        RX_STR_PKT_AFULL  (0) => gen_afull                       ,

        SPACE_GLB_RD_PTR      => rd_ptr     ,
        SPACE_GLB_WR_PTR      => wr_ptr     ,

        TX_GLB_PKT_META       => open       ,
        TX_GLB_PKT_LEN        => pkt_len    ,
        TX_GLB_PKT_ADDR       => pkt_addr   ,
        TX_GLB_PKT_VLD        => pkt_vld    ,
        TX_GLB_PKT_DST_RDY    => pkt_dst_rdy
    );

    GEN_ACCEPT <= (others => (not gen_afull));

    pkt_sptr <= pkt_addr;
    pkt_eptr_gen : for i in 0 to REGIONS-1 generate
        pkt_eptr(i) <= std_logic_vector(unsigned(pkt_sptr(i))+resize_left(unsigned(pkt_len(i)),log2(SPACE_SIZE))-1);
    end generate;

    pkt_dst_rdy_gen : for i in 0 to REGIONS-1 generate
        -- Read when TX is ready and the packet starts in the current word
        pkt_dst_rdy(i) <= '1' when (TX_MFB_DST_RDY='1' and pkt_curr_word='1' and resize_right(unsigned(pkt_sptr(i)),log2(SPACE_WORDS))=rd_ptr_used) or is_stopped='1' else '0';
    end generate;

    -- Check if the current output starts in the word pointed to by rd_ptr_used
    pkt_curr_word <= '1' when resize_right(unsigned(pkt_sptr(0)),log2(SPACE_WORDS))=rd_ptr_used else '0';

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- RD PTR
    ----------------------------------------------------------------------------

    rd_ptr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (TX_MFB_DST_RDY='1') then
                -- Increments by words
                rd_ptr_reg <= rd_ptr_used+1;
            end if;
        end if;
    end process;

    -- If the current packet starts in the previous word, roll RD_PTR back to this word
    rd_ptr_dec  <= rd_ptr_reg-1;
    rd_ptr_used <= rd_ptr_dec when pkt_vld(0)='1' and resize_right(unsigned(pkt_sptr(0)),log2(SPACE_WORDS))=rd_ptr_dec and is_stopped='0' else rd_ptr_reg;

    -- Simulate always-empty buffer
    rd_ptr <= wr_ptr;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Reg 0
    ----------------------------------------------------------------------------

    reg0_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_MFB_DST_RDY='1') then
                reg0_ptr  <= rd_ptr_used;
                reg0_sptr <= pkt_sptr;
                reg0_eptr <= pkt_eptr;
                reg0_vld  <= pkt_vld and pkt_dst_rdy;
            end if;

            if (RESET='1' or is_stopped='1') then
                reg0_vld <= (others => '0');
            end if;
        end if;
    end process;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Prev Reg
    ----------------------------------------------------------------------------
    -- Stores EOF PTR from a packet that contiues from a previous word.

    reg0_prv_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_MFB_DST_RDY='1') then
                reg0_prev_vld <= '0';
                for i in 0 to REGIONS+1-1 loop
                    -- Store the packet EOF PTR when it is valid and ends in a different word.
                    -- This condition should allways be TRUE for only one packet or none of them.
                    if (reg0_evld_vec(i)='1' and resize_right(reg0_eptr_vec(i),log2(SPACE_WORDS))/=reg0_ptr) then
                        reg0_prev_eptr <= reg0_eptr_vec(i);
                        reg0_prev_vld  <= reg0_evld_vec(i);
                    end if;
                end loop;
            end if;

            if (RESET='1') then
                reg0_prev_vld <= '0';
            end if;
        end if;
    end process;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Reg 0 to Reg 1 vectors
    ----------------------------------------------------------------------------

    reg0_eptr_vec(0) <= reg0_prev_eptr;
    ptr_vec_gen : for i in 0 to REGIONS-1 generate
        reg0_sptr_vec(i)   <= unsigned(reg0_sptr(i));
        reg0_eptr_vec(i+1) <= unsigned(reg0_eptr(i));
    end generate;
    reg0_svld_vec <= reg0_vld;
    reg0_evld_vec <= reg0_vld & reg0_prev_vld;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Reg 1
    ----------------------------------------------------------------------------

    reg1_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_MFB_DST_RDY='1') then

                reg1_svld  <= (others => '0');
                reg1_evld  <= (others => '0');

                for i in 0 to REGIONS-1 loop

                    for e in 0 to REGIONS-1 loop
                        -- If valid SOF pointing to this word and this region
                        if (reg0_svld_vec(e)='1' and resize_right(reg0_sptr_vec(e),log2(SPACE_WORDS))=reg0_ptr and (resize_right(resize_left(reg0_sptr_vec(e),log2(WORD_ITEMS)),log2(REGIONS))=i or REGIONS<2)) then
                            reg1_sptr(i) <= reg0_sptr_vec(e);
                            reg1_svld(i) <= '1';
                        end if;
                    end loop;

                    for e in 0 to REGIONS+1-1 loop
                        -- If valid EOF pointing to this word and this region
                        if (reg0_evld_vec(e)='1' and resize_right(reg0_eptr_vec(e),log2(SPACE_WORDS))=reg0_ptr and (resize_right(resize_left(reg0_eptr_vec(e),log2(WORD_ITEMS)),log2(REGIONS))=i or REGIONS<2)) then
                            reg1_eptr(i) <= reg0_eptr_vec(e);
                            reg1_evld(i) <= '1';
                        end if;
                    end loop;

                end loop;
            end if;

            if (RESET='1') then
                reg1_svld  <= (others => '0');
                reg1_evld  <= (others => '0');
            end if;
        end if;
    end process;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- MFB in frame register
    ----------------------------------------------------------------------------

    tx_mfb_inframe_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            if (TX_MFB_DST_RDY='1') then

                -- Invert when the number of SOFs is different from the number of EOFs (can only differ by 0 or 1).
                if ((xor (reg1_svld & reg1_evld))='1') then
                    tx_mfb_inframe <= not tx_mfb_inframe;
                end if;

            end if;

            if (RESET='1') then
                tx_mfb_inframe <= '0';
            end if;
        end if;
    end process;

    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- TX MFB generation
    ----------------------------------------------------------------------------

    TX_MFB_SOF <= reg1_svld;
    TX_MFB_EOF <= reg1_evld;

    tx_mfb_pos_gen : for i in 0 to REGIONS-1 generate
        TX_MFB_SOF_POS_arr(i) <= std_logic_vector(resize_left(resize_right(resize_left(reg1_sptr(i),log2(REGION_ITEMS)),log2(REGION_SIZE)),max(1,log2(REGION_SIZE))));
        TX_MFB_EOF_POS_arr(i) <= std_logic_vector(resize_left(resize_right(resize_left(reg1_eptr(i),log2(REGION_ITEMS)),log2(REGION_SIZE*BLOCK_SIZE)),max(1,log2(REGION_SIZE*BLOCK_SIZE))));
    end generate;

    TX_MFB_SOF_POS <= slv_array_ser(TX_MFB_SOF_POS_arr);
    TX_MFB_EOF_POS <= slv_array_ser(TX_MFB_EOF_POS_arr);

    TX_MFB_SRC_RDY <= tx_mfb_inframe or (or reg1_svld);

    ----------------------------------------------------------------------------

end architecture;
