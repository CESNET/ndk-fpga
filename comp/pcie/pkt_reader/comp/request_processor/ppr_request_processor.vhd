-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;
use work.dma_bus_pack.all;


-- This module prepares DMA Upstream headers to download the requested data.
-- It also creates records to memories that store and update the state of responses:
--
--   #. a record to the ID memory (stores packet-level state: base address, word count, EOF position, tag count),
--   #. a record to the Tag memory (stores transaction-level state: write address, packet ID for each PCIe tag).
--
-- Issues backpressure for user requests when not enough space in the Main Memory is detected.
--
entity PPR_REQUEST_PROCESSOR is
    generic (
        -- Number of MVB Items in a word, can't handle more than 1.
        MVB_ITEMS         : natural := 1;
        -- Maximum packet size (in bytes).
        PKT_MTU           : natural := 2**12;
        -- Size of the Main Memory for responses, in number of stored words.
        MEMORY_ITEMS      : natural := 2048;
        -- Size of each Item in the Main Memory (in bits).
        MEMORY_ITEM_WIDTH : natural := 1*8*8*8;
        ID_WIDTH          : natural := 11;
        PCIE_MRRS_WIDTH   : natural := 13;
        -- Size of a RAM page (in bytes).
        PAGE_SIZE         : natural := 4096;
        DEVICE            : string := "AGILEX"
    );
    port (
        CLK               : in std_logic;
        RESET             : in std_logic;

        -- Specifies the currently configured PCIe Maximum Read Request Size (in bytes).
        -- PCIe specification allows at least 128.
        PCIE_MRRS         : in  std_logic_vector(PCIE_MRRS_WIDTH-1 downto 0);

        -- ========================================================
        -- RX Interface
        -- ========================================================

        RX_MVB_ID         : in  std_logic_vector(MVB_ITEMS*ID_WIDTH-1 downto 0);
        RX_MVB_ADDRESS    : in  std_logic_vector(MVB_ITEMS*DMA_REQUEST_GLOBAL_W-1 downto 0);
        RX_MVB_LENGTH     : in  std_logic_vector(MVB_ITEMS*log2(PKT_MTU+1)-1 downto 0);
        RX_MVB_VLD        : in  std_logic_vector(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY    : in  std_logic;
        RX_MVB_DST_RDY    : out std_logic;

        -- ========================================================
        -- TX Interfaces
        -- ========================================================

        TX_MVB_DATA       : out std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
        TX_MVB_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY    : out std_logic;
        TX_MVB_DST_RDY    : in  std_logic;

        -- IDMEM Address (key) to store the following data.
        IDMEM_ID          : out std_logic_vector(MVB_ITEMS*ID_WIDTH-1 downto 0);
        -- IDMEM Data part 0 - address of a packets SOF in the Main Memory.
        IDMEM_ADDR        : out std_logic_vector(MVB_ITEMS*log2(MEMORY_ITEMS)+1-1 downto 0);
        -- IDMEM Data part 1 - maximum number of words an MTU can consist of.
        IDMEM_WORDS       : out std_logic_vector(MVB_ITEMS*log2(div_roundup(PKT_MTU+1,MEMORY_ITEM_WIDTH/8))-1 downto 0);
        -- IDMEM Data part 2 - a packet's end position throughout the whole word.
        IDMEM_EOF_POS     : out std_logic_vector(MVB_ITEMS*log2(MEMORY_ITEM_WIDTH/8)-1 downto 0);
        -- IDMEM Data part 3 - the amount of Tags (Read requests) used for this packet's transmission.
        IDMEM_TAG_CNT     : out std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
        -- IDMEM record valid / write request
        IDMEM_VLD         : out std_logic_vector(MVB_ITEMS-1 downto 0);

        -- TAGMEM Address (key) to store the data.
        TAGMEM_TAG        : out std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
        -- TAGMEM Data part 0 - address of a response's SOF in the Main Memory.
        TAGMEM_ADDR       : out std_logic_vector(MVB_ITEMS*(log2(MEMORY_ITEMS)+log2(MEMORY_ITEM_WIDTH/8))-1 downto 0);
        -- TAGMEM Data part 1 - identifier of the packet this Tag (Read response) belongs to.
        TAGMEM_ID         : out std_logic_vector(MVB_ITEMS*ID_WIDTH-1 downto 0);
        -- TAGMEM Data part 2 - First Invalid Bytes - compensation for word alignment of the address.
        TAGMEM_FIRSTIB    : out std_logic_vector(MVB_ITEMS*DMA_REQUEST_FIRSTIB_W-1 downto 0);
        -- TAGMEM Data part 3 - Last Invalid Bytes - compensation for word alignment of the packet's end.
        TAGMEM_LASTIB     : out std_logic_vector(MVB_ITEMS*DMA_REQUEST_FIRSTIB_W-1 downto 0);
        -- TAGMEM record valid / write request.
        TAGMEM_VLD        : out std_logic_vector(MVB_ITEMS-1 downto 0);

        -- Receives freed tags for reuse.
        TAGMEM_FREE_TAG   : in  std_logic_vector(MVB_ITEMS*DMA_REQUEST_TAG_W-1 downto 0);
        TAGMEM_FREE_VLD   : in  std_logic_vector(MVB_ITEMS-1 downto 0);

        -- Current read pointer of the Main Memory - for congestion control (memory full).
        MEM_RD_PTR        : in  std_logic_vector(log2(MEMORY_ITEMS)+1-1 downto 0)

    );
end entity;

architecture FULL of PPR_REQUEST_PROCESSOR is

    -- =====================================================================
    --                                CONSTANTS
    -- =====================================================================

    -- DMA_REQUEST_LENGTH_W extended by 2 bits (conversion from Dwords to Bytes).
    constant DMA_REQUEST_LENGTH_W_EXT : natural := DMA_REQUEST_LENGTH_W + 2;

    -- Base meta width. Contains:              orignal pkt len + pkt's ID
    constant META_WIDTH_BASE      : natural := log2(PKT_MTU+1) + ID_WIDTH;
    -- Extended meta width. Contains:          Last + partial pkt len + META_WIDTH_BASE
    constant META_WIDTH_EXT       : natural := 1    + PCIE_MRRS_WIDTH + META_WIDTH_BASE;

    -- Width of a base address that identifies the word in the Main Memory.
    constant MEM_BASE_ADDR_WIDTH  : natural := log2(MEMORY_ITEMS);
    -- Identifies a byte within the word (item) in the Main Memory.
    constant MEM_WORD_ADDR_WIDTH  : natural := log2(MEMORY_ITEM_WIDTH/8);
    -- Combined address of the previous two: higher bits identify ITEM, lower bits identify BYTE.
    constant MEM_COMB_ADDR_WIDTH  : natural := MEM_BASE_ADDR_WIDTH + MEM_WORD_ADDR_WIDTH;

    -- =====================================================================
    --                                 SIGNALS
    -- =====================================================================

    signal rx_mvb_id_arr             : slv_array_t(MVB_ITEMS-1 downto 0)(ID_WIDTH-1 downto 0);
    signal rx_mvb_length_arr         : slv_array_t(MVB_ITEMS-1 downto 0)(log2(PKT_MTU+1)-1 downto 0);
    signal rx_meta_arr               : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH_BASE-1 downto 0);

    signal instr_tx_meta             : std_logic_vector(MVB_ITEMS*META_WIDTH_BASE-1 downto 0);
    signal instr_tx_address          : std_logic_vector(MVB_ITEMS*DMA_REQUEST_GLOBAL_W-1 downto 0);
    signal instr_tx_length           : std_logic_vector(MVB_ITEMS*PCIE_MRRS_WIDTH-1 downto 0);
    signal instr_tx_last             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal instr_tx_valid            : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal instr_tx_src_rdy          : std_logic;
    signal instr_tx_dst_rdy          : std_logic;

    signal instr_tx_meta_arr         : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH_BASE-1 downto 0);
    signal instr_tx_length_arr       : slv_array_t(MVB_ITEMS-1 downto 0)(PCIE_MRRS_WIDTH-1 downto 0);
    signal hdrgen_rx_meta_arr        : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH_EXT-1 downto 0);

    signal hdrgen_tx_data            : std_logic_vector(MVB_ITEMS*DMA_UPHDR_WIDTH-1 downto 0);
    signal hdrgen_tx_meta            : std_logic_vector(MVB_ITEMS*META_WIDTH_EXT-1 downto 0);
    signal hdrgen_tx_vld             : std_logic_vector(MVB_ITEMS-1 downto 0);
    signal hdrgen_tx_src_rdy         : std_logic;
    signal hdrgen_tx_dst_rdy         : std_logic;

    signal hdrgen_tx_meta_arr        : slv_array_t(MVB_ITEMS-1 downto 0)(META_WIDTH_EXT-1 downto 0);
    signal hdrgen_tx_id              : std_logic_vector(ID_WIDTH-1 downto 0);
    signal hdrgen_tx_full_length     : std_logic_vector(log2(PKT_MTU+1)-1 downto 0);
    signal hdrgen_tx_partial_length  : std_logic_vector(PCIE_MRRS_WIDTH-1 downto 0);
    signal hdrgen_tx_last            : std_logic;
    signal hdr_valid                 : std_logic;
    signal idmem_record_vld          : std_logic;

    signal main_mem_base_addr        : unsigned(MEM_BASE_ADDR_WIDTH+1-1 downto 0); -- +1 bit to detect full
    signal main_mem_base_addr_new    : unsigned(MEM_BASE_ADDR_WIDTH+1-1 downto 0); -- +1 bit to detect full
    signal hdrgen_tx_full_length_res : unsigned(MEM_COMB_ADDR_WIDTH-1 downto 0);
    signal words                     : unsigned(MEM_BASE_ADDR_WIDTH-1 downto 0);
    signal words_rounded_up          : unsigned(MEM_BASE_ADDR_WIDTH-1 downto 0);
    signal wr_ptr_catching_up        : std_logic;
    signal wr_addr_gt_rd_addr        : std_logic;
    signal main_mem_full             : std_logic;
    signal eofpos_offset             : unsigned(log2(PKT_MTU+1)-1 downto 0);
    signal tag_cnt                   : unsigned(DMA_REQUEST_TAG_W-1 downto 0);

    signal main_mem_partial_addr     : unsigned(MEM_COMB_ADDR_WIDTH-1 downto 0);

begin

    -- =====================================================================
    --  Instruction Generator borrowed from the PCIe Packet Writer
    -- =====================================================================

    rx_mvb_id_arr     <= slv_array_deser(RX_MVB_ID, MVB_ITEMS);
    rx_mvb_length_arr <= slv_array_deser(RX_MVB_LENGTH, MVB_ITEMS);

    rx_meta_g : for i in 0 to MVB_ITEMS-1 generate
        rx_meta_arr(i) <= rx_mvb_length_arr(i) & rx_mvb_id_arr(i);
    end generate;

    instr_generator_i : entity work.PPW_INSTR_GEN
    generic map (
        MVB_ITEMS      => MVB_ITEMS,
        MVB_META_WIDTH => META_WIDTH_BASE,
        PKT_MTU        => PKT_MTU,
        PCIE_MPS_WIDTH => PCIE_MRRS_WIDTH,
        ADDRESS_WIDTH  => DMA_REQUEST_GLOBAL_W,
        PAGE_SIZE      => PAGE_SIZE,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        PCIE_MPS       => PCIE_MRRS,

        RX_MVB_META    => slv_array_ser(rx_meta_arr),
        RX_MVB_ADDRESS => RX_MVB_ADDRESS,
        RX_MVB_LENGTH  => RX_MVB_LENGTH,
        RX_MVB_VALID   => RX_MVB_VLD,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY,

        TX_MVB_META    => instr_tx_meta,
        TX_MVB_ADDRESS => instr_tx_address,
        TX_MVB_LENGTH  => instr_tx_length,
        TX_MVB_LAST    => instr_tx_last,
        TX_MVB_VALID   => instr_tx_valid,
        TX_MVB_SRC_RDY => instr_tx_src_rdy,
        TX_MVB_DST_RDY => instr_tx_dst_rdy
    );

    -- =====================================================================
    --  DMA UpHeader Generator
    -- =====================================================================

    instr_tx_meta_arr   <= slv_array_deser(instr_tx_meta, MVB_ITEMS);
    instr_tx_length_arr <= slv_array_deser(instr_tx_length, MVB_ITEMS);
    hdrgen_rx_meta_g : for i in 0 to MVB_ITEMS-1 generate
        hdrgen_rx_meta_arr(i) <= instr_tx_last(i) & instr_tx_length_arr(i) & instr_tx_meta_arr(i);
    end generate;

    dma_uphdr_gen_i : entity work.PPR_DMA_UPHDR_GEN
    generic map (
        MVB_ITEMS      => MVB_ITEMS,
        MVB_META_WIDTH => META_WIDTH_EXT,
        PKT_MTU        => 2**DMA_REQUEST_LENGTH_W_EXT-1,
        DEVICE         => DEVICE
    )
    port map (
        CLK            => CLK,
        RESET          => RESET,

        RX_MVB_META    => slv_array_ser(hdrgen_rx_meta_arr),
        RX_MVB_ADDRESS => instr_tx_address,
        RX_MVB_LENGTH  => std_logic_vector(resize(unsigned(instr_tx_length),DMA_REQUEST_LENGTH_W_EXT)),
        RX_MVB_VALID   => instr_tx_valid,
        RX_MVB_SRC_RDY => instr_tx_src_rdy,
        RX_MVB_DST_RDY => instr_tx_dst_rdy,

        TX_MVB_DATA    => hdrgen_tx_data,
        TX_MVB_META    => hdrgen_tx_meta,
        TX_MVB_VLD     => hdrgen_tx_vld,
        TX_MVB_SRC_RDY => hdrgen_tx_src_rdy,
        TX_MVB_DST_RDY => hdrgen_tx_dst_rdy,

        FREE_TAG       => TAGMEM_FREE_TAG,
        FREE_VLD       => TAGMEM_FREE_VLD
    );

    hdrgen_tx_dst_rdy <= TX_MVB_DST_RDY and not main_mem_full;

    hdrgen_tx_meta_arr <= slv_array_deser(hdrgen_tx_meta, MVB_ITEMS);

    -- hdrgen_tx_last: indicates the last partial instruction of the original instruction on input.
    -- hdrgen_tx_partial_length: the length in the partial instruction.
    -- hdrgen_tx_full_length: the length of the complete packet, duplicated for all partial instructions.
    -- hdrgen_tx_id: ID of the complete packet, duplicated for all partial instructions.
    (hdrgen_tx_last, hdrgen_tx_partial_length, hdrgen_tx_full_length, hdrgen_tx_id) <= hdrgen_tx_meta_arr(0);

    hdr_valid <= hdrgen_tx_src_rdy and hdrgen_tx_vld(0);

    -- =====================================================================
    --  DMA UpHeader output
    -- =====================================================================

    TX_MVB_DATA    <= hdrgen_tx_data;
    TX_MVB_VLD     <= hdrgen_tx_vld;
    TX_MVB_SRC_RDY <= hdrgen_tx_src_rdy and not main_mem_full;

    -- =====================================================================
    --  ID Memory logic
    -- =====================================================================

    -- ---------------------------------------------------------------------
    --  Main Memory base address & Words logic
    -- ---------------------------------------------------------------------
    -- Current addres + the amount of words of this packet will already point to the next free word.
    main_mem_base_addr_new <= main_mem_base_addr + words_rounded_up;
    process (CLK)
    begin
        if rising_edge(CLK) then
            if (idmem_record_vld = '1') then
                main_mem_base_addr <= main_mem_base_addr_new;
            end if;
            if (RESET = '1') then
                main_mem_base_addr <= (others => '0');
            end if;
        end if;
    end process;

    -- Assert in the top-level should make sure it is never shortened.
    hdrgen_tx_full_length_res <= resize(unsigned(hdrgen_tx_full_length), MEM_COMB_ADDR_WIDTH);
    -- The number of words in the Main Memory will be occupied by the packet of this Length.
    words                     <= hdrgen_tx_full_length_res(MEM_COMB_ADDR_WIDTH-1 downto MEM_WORD_ADDR_WIDTH);
    words_rounded_up          <= words + (or hdrgen_tx_full_length(MEM_WORD_ADDR_WIDTH-1 downto 0));

    -- ---------------------------------------------------------------------
    --  Main Memory full logic
    -- ---------------------------------------------------------------------
    -- Write pointer is catching up to the Read pointer when the top bits do not have the same value.
    wr_ptr_catching_up <= MEM_RD_PTR(MEM_BASE_ADDR_WIDTH) xor main_mem_base_addr_new(MEM_BASE_ADDR_WIDTH);
    -- the Write pointer is greater than the Read pointer.
    wr_addr_gt_rd_addr <= '1' when (unsigned(MEM_RD_PTR(MEM_BASE_ADDR_WIDTH-1 downto 0)) <= main_mem_base_addr_new(MEM_BASE_ADDR_WIDTH-1 downto 0)) else '0';
    -- Overflow (full) occurs after the Writer pointer is greater then Read pointer and the Write pointer is one "loop" ahead in the address space.
    main_mem_full      <= wr_ptr_catching_up and wr_addr_gt_rd_addr;

    -- ---------------------------------------------------------------------
    --  EOF POS logic
    -- ---------------------------------------------------------------------
    -- Turn Length into pointer to EOF POS.
    eofpos_offset <= unsigned(hdrgen_tx_full_length) - 1;

    -- ---------------------------------------------------------------------
    --  Tag count logic
    -- ---------------------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((hdr_valid = '1') and (hdrgen_tx_dst_rdy = '1')) then
                tag_cnt <= tag_cnt + 1;
            end if;
            if ((RESET = '1') or (idmem_record_vld = '1')) then
                tag_cnt <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================
    --  ID Memory output
    -- =====================================================================

    idmem_record_vld <= not main_mem_full and hdr_valid and hdrgen_tx_last and TX_MVB_DST_RDY;
    process (CLK)
    begin
        if rising_edge(CLK) then
            IDMEM_ID      <= hdrgen_tx_id;
            IDMEM_ADDR    <= std_logic_vector(main_mem_base_addr);
            IDMEM_WORDS   <= std_logic_vector(resize(words_rounded_up, IDMEM_WORDS'length));
            IDMEM_EOF_POS <= std_logic_vector(eofpos_offset(MEM_WORD_ADDR_WIDTH-1 downto 0));
            IDMEM_TAG_CNT <= std_logic_vector(tag_cnt + 1);
            IDMEM_VLD     <= (others => idmem_record_vld);
            if (RESET = '1') then
                IDMEM_VLD <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================
    --  Tag Memory logic
    -- =====================================================================

    -- ---------------------------------------------------------------------
    --  Main Memory partial address logic
    -- ---------------------------------------------------------------------
    process (CLK)
    begin
        if rising_edge(CLK) then
            if ((hdr_valid = '1') and (hdrgen_tx_dst_rdy = '1')) then
                main_mem_partial_addr <= main_mem_partial_addr + unsigned(hdrgen_tx_partial_length);
            end if;
            if ((RESET = '1') or (idmem_record_vld = '1')) then
                main_mem_partial_addr <= (others => '0');
            end if;
        end if;
    end process;

    -- =====================================================================
    --  Tag Memory output
    -- =====================================================================

    process (CLK)
    begin
        if rising_edge(CLK) then
            TAGMEM_TAG     <= hdrgen_tx_data(DMA_REQUEST_TAG);
            TAGMEM_ADDR    <= std_logic_vector(resize_right(main_mem_base_addr(MEM_BASE_ADDR_WIDTH-1 downto 0), MEM_COMB_ADDR_WIDTH) + main_mem_partial_addr);
            TAGMEM_ID      <= hdrgen_tx_id;
            TAGMEM_FIRSTIB <= hdrgen_tx_data(DMA_REQUEST_FIRSTIB);
            TAGMEM_LASTIB  <= hdrgen_tx_data(DMA_REQUEST_LASTIB);
            TAGMEM_VLD     <= (others => hdr_valid and hdrgen_tx_dst_rdy);
            if (RESET = '1') then
                TAGMEM_VLD <= (others => '0');
            end if;
        end if;
    end process;

end architecture;
