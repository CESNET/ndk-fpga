-- rx_dma_calypte_hdr_insertor.vhd: inserts PCIex header to each transfer and sends DMA header afterwards
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- Note: The documentation uses the terms "word" and "region" with concardance to the MFB
-- specification. Word is a particular clock cycle of a MFB vector, meaning f.e. RX_MFB_DATA or
-- TX_MFB_DATA. This word can contain N regions starting from 1 which is configured by TX_REGIONS
-- generic parameter. The clock cycle is also called a "beat" or "bus beat".

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;
use work.pcie_hdr_fields_pkg.all;

-- This component accepts buffered PCIe transactions (currently set to the
-- length of 128 Bytes). And sends them with appropriate PCIe header. When end of a
-- packet is processed, the DMA header is sent after that in a separate transaction.
entity RX_DMA_CALYPTE_HDR_INSERTOR is
    generic (
        -- =========================================================================================
        -- RX MFB configuration
        --
        -- Number of regions is always 1
        -- =========================================================================================
        RX_REGION_SIZE : natural := 1;
        RX_BLOCK_SIZE  : natural := 128;
        RX_ITEM_WIDTH  : natural := 8;

        -- =========================================================================================
        -- TX MFB configuration
        -- =========================================================================================
        TX_REGIONS     : natural := 2;
        TX_REGION_SIZE : natural := 1;
        TX_BLOCK_SIZE  : natural := 8;
        TX_ITEM_WIDTH  : natural := 32;

        DEVICE       : string  := "ULTRASCALE"
    );
    port (
        CLK : in std_logic;
        RST : in std_logic;

        -- =========================================================================================
        -- MFB input interface
        --
        -- EOF_POS is not used because. when the input word ends (signalized by EOF), whole word is
        -- valid. The SOF_POS is not used either because the input words are aligned to the
        -- beginning of the word.
        -- =========================================================================================
        RX_MFB_DATA    : in  std_logic_vector(RX_REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
        RX_MFB_SOF     : in  std_logic;
        RX_MFB_EOF     : in  std_logic;
        RX_MFB_EOF_POS : in  std_logic_vector (max(1, log2(RX_REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic;
        RX_MFB_DST_RDY : out std_logic;

        -- =========================================================================================
        -- MFB output interface
        -- =========================================================================================
        TX_MFB_DATA    : out std_logic_vector(TX_REGIONS*TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
        -- RQ PCIe header
        TX_MFB_META    : out std_logic_vector(TX_REGIONS*PCIE_RQ_META_WIDTH - 1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(TX_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(TX_REGIONS*max(1, log2(TX_REGION_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(TX_REGIONS*max(1, log2(TX_REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic;

        -- =========================================================================================
        -- Header manager MVB interface
        -- =========================================================================================
        HDRM_DMA_PCIE_HDR         : in  std_logic_vector(127 downto 0);
        HDRM_DMA_PCIE_HDR_SRC_RDY : in  std_logic;
        HDRM_DMA_PCIE_HDR_DST_RDY : out std_logic;

        HDRM_DATA_PCIE_HDR         : in  std_logic_vector(127 downto 0);
        HDRM_DATA_PCIE_HDR_SRC_RDY : in  std_logic;
        HDRM_DATA_PCIE_HDR_DST_RDY : out std_logic;

        HDRM_PKT_DROP        : in  std_logic;
        HDRM_DMA_HDR_DATA    : in  std_logic_vector(63 downto 0);
        HDRM_DMA_HDR_SRC_RDY : in  std_logic;
        HDRM_DMA_HDR_DST_RDY : out std_logic
    );
end entity;

architecture FULL of RX_DMA_CALYPTE_HDR_INSERTOR is

    -- On Intel devices, the PCIe header is sent in a TX_MFB_META bus separated from the data on the
    -- TX_MFB_DATA.
    constant IS_INTEL         : boolean := (DEVICE = "STRATIX10") or (DEVICE = "AGILEX");

    signal bshifter_data_out  : std_logic_vector(RX_MFB_DATA'range);
    signal low_shift_val      : std_logic;
    -- normally the lenght of these signals is set to address each group of 4 blocks on the bus but I made the
    -- signals one bit wider because I use them as a counter of output words in each transaction
    signal high_shift_val_pst : unsigned(log2(32)-4 downto 0);
    signal high_shift_val_nst : unsigned(log2(32)-4 downto 0);

    type   tran_process_state_type is (IDLE, TRANSACTION_SEND, DMA_HDR_SEND, PKT_DROP);
    signal tprocess_pst : tran_process_state_type := IDLE;
    signal tprocess_nst : tran_process_state_type := IDLE;

    constant TX_EOF_POS_RGN_LEN : positive := maximum(1, log2(TX_REGION_SIZE*TX_BLOCK_SIZE));
    signal   tx_mfb_meta_arr    : slv_array_t(TX_REGIONS-1 downto 0)(PCIE_RQ_META_WIDTH-1 downto 0);
    signal   tx_mfb_eof_pos_arr : slv_array_t(TX_REGIONS-1 downto 0)(TX_EOF_POS_RGN_LEN -1 downto 0);

    -- varies its value according to the generic parameters
    signal shift_inc  : unsigned(1 downto 0);
    signal init_shift : unsigned(1 downto 0);

    -- attribute mark_debug                       : string;
    -- attribute mark_debug of tprocess_pst       : signal is "true";
    -- attribute mark_debug of high_shift_val_pst : signal is "true";
begin

    assert ((RX_REGION_SIZE = 1 and RX_BLOCK_SIZE = 128 and RX_ITEM_WIDTH = 8)
            or (RX_REGION_SIZE = 1 and RX_BLOCK_SIZE = 256 and RX_ITEM_WIDTH = 8))
        report "RX_DMA_HDR_INSERTOR: The design is not prepared for such RX MFB configuration, the valid are: MFB#(_,1,128,8), MFB#(_,1,256,8)."
        severity FAILURE;

    assert ((TX_REGIONS = 1 and TX_REGION_SIZE = 1 and TX_BLOCK_SIZE = 8 and TX_ITEM_WIDTH = 32)
            or (TX_REGIONS = 2 and TX_REGION_SIZE = 1 and TX_BLOCK_SIZE = 8 and TX_ITEM_WIDTH = 32))
        report "RX_DMA_HDR_INSERTOR: The design is not prepared for such TX MFB configuration, the valid are: MFB#(1,1,8,32), MFB#(2,1,8,32)."
        severity FAILURE;

    -- psl rd_dma_fifo_empty :
    --      assert always (HDRM_DMA_HDR_DST_RDY -> HDRM_DMA_HDR_SRC_RDY) abort (RST) @rising_edge(CLK)
    --      report "RX_DMA_HDR_INSERTOR: Reading from the DMA Header FIFO can only occur if there are some data!";

    -- psl rd_dma_pcie_fifo_empty :
    --      assert always (HDRM_DMA_PCIE_HDR_DST_RDY -> HDRM_DMA_PCIE_HDR_SRC_RDY) abort (RST) @rising_edge(CLK)
    --      report "RX_DMA_HDR_INSERTOR: Reading from the DMA PCIe Header FIFO can only occur if there are some data!";

    -- psl rd_data_pcie_fifo_empty :
    --      assert always (HDRM_DATA_PCIE_HDR_DST_RDY -> HDRM_DATA_PCIE_HDR_SRC_RDY) abort (RST) @rising_edge(CLK)
    --      report "RX_DMA_HDR_INSERTOR: Reading from the data PCIe Header FIFO can only occur if there are some data!";

    --=============================================================================================================
    -- FSM state register
    --=============================================================================================================
    -- We still need shift data even though it's intel
    tprocess_pst_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                tprocess_pst       <= IDLE;
            else
                tprocess_pst       <= tprocess_nst;
            end if;
        end if;
    end process;

    high_shift_val_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then
                if (not IS_INTEL) then
                    high_shift_val_pst <= "11";
                else
                    high_shift_val_pst <= "00";
                end if;
            elsif (TX_MFB_DST_RDY = '1') then
                high_shift_val_pst <= high_shift_val_nst;
            end if;
        end if;
    end process;

    tprocess_amd_1_rgn_g : if ((not IS_INTEL) and TX_REGIONS = 1) generate
        tprocess_nst_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
        begin
            tprocess_nst     <= tprocess_pst;
            rx_mfb_eof_pos_u := resize(unsigned(RX_MFB_EOF_POS), rx_mfb_eof_pos_u'length);

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif ((not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) and HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                            -- If the current input word does not fit into one output word, then
                            -- proceed normally.
                            if (RX_MFB_EOF = '0' or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 16)) then
                                tprocess_nst <= TRANSACTION_SEND;

                            -- If a current input word fits into one output one, then send a DMA
                            -- header in the next word.
                            else
                                tprocess_nst <= DMA_HDR_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (TX_MFB_DST_RDY = '1') then
                        if (RX_MFB_EOF = '1'
                            and (16 + (resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32 > rx_mfb_eof_pos_u)
                        ) then
                            tprocess_nst <= DMA_HDR_SEND;

                        elsif (RX_MFB_EOF = '0' and high_shift_val_pst = "11") then
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    if (TX_MFB_DST_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
        begin
            rx_mfb_eof_pos_u := resize(unsigned(RX_MFB_EOF_POS), rx_mfb_eof_pos_u'length);

            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                -- In this state, the component waits for the arrival of three crucial components,
                -- a valid packet, the PCIE header and the DMA header
                when IDLE =>
                    -- If arrived word is a one-word output transaction and its PCIE Header is
                    -- ready, then dispatch the transaction and switch to a next word
                    if (RX_MFB_SRC_RDY = '1' and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        if (RX_MFB_EOF = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1' and rx_mfb_eof_pos_u < 16) then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                    -- awaiting the arrival of valid DMA header with the information if packet
                    -- should be dropped or not
                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_PKT_DROP = '1') then
                        RX_MFB_DST_RDY <= '1';

                        -- if valid EOF is captured, current DMA header is also dropped (the
                        -- case of a one-word transaction)
                        if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                            HDRM_DMA_HDR_DST_RDY <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (RX_MFB_EOF = '1'
                        and ((16 + (resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32) > rx_mfb_eof_pos_u)
                    ) then

                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;

                    elsif (RX_MFB_EOF = '0' and high_shift_val_pst = "11") then
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY      <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= '1';

                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= '1';
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
            variable rx_mfb_eof_pos_u   : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable trans_byte_length  : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable data_pcie_hdr_corr : std_logic_vector(HDRM_DATA_PCIE_HDR'range);
        begin
            high_shift_val_nst <= high_shift_val_pst;
            rx_mfb_eof_pos_u   := resize(unsigned(RX_MFB_EOF_POS), rx_mfb_eof_pos_u'length);

            tx_mfb_meta_arr                      <= (others => (others => '0'));
            tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= (others => '1');
            tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= (others => '1');

            TX_MFB_DATA     <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF      <= (others => '0');
            TX_MFB_EOF      <= (others => '0');
            TX_MFB_SOF_POS  <= (others => '0');
            TX_MFB_EOF_POS  <= (others => '0');
            TX_MFB_SRC_RDY  <= '0';

            data_pcie_hdr_corr := HDRM_DATA_PCIE_HDR;
            trans_byte_length  := resize(rx_mfb_eof_pos_u, rx_mfb_eof_pos_u'length) + 1;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        -- Correct the DW count in the header
                        if (RX_MFB_EOF = '1') then
                            data_pcie_hdr_corr(A_RQ_HDR_DWORD_CNT) := std_logic_vector(resize(rx_mfb_eof_pos_u(rx_mfb_eof_pos_u'high-1 downto 2), A_RQ_HDR_DWORD_CNT_W) + 1);

                            case trans_byte_length is
                                when to_unsigned(1, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0001";
                                when to_unsigned(2, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0011";
                                when to_unsigned(3, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0111";
                                when others => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "1111";
                            end case;

                            if (trans_byte_length > 4) then
                                case trans_byte_length(1 downto 0) is
                                    when "00" => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "1111";
                                    when "01" => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0001";
                                    when "10" => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0011";
                                    when "11" => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0111";
                                    when others => null;
                                end case;
                            else
                                tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0000";
                            end if;
                        end if;

                        TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 128) & data_pcie_hdr_corr;
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_SRC_RDY     <= '1';

                        if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 16) then
                            TX_MFB_EOF     <= "1";
                            -- The value is the EOF_POS in DWs (the RX_MFB_EOF_POS is in bytes)
                            -- derived from the RX_MFB_EOF_POS incremented by the size of the PCIe header.
                            TX_MFB_EOF_POS <= std_logic_vector(rx_mfb_eof_pos_u(TX_MFB_EOF_POS'high + 2 downto 2) + 4);
                        else
                            high_shift_val_nst <= init_shift;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if ((RX_MFB_EOF = '1'
                         and ((16 + (resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32) > rx_mfb_eof_pos_u))
                        or (RX_MFB_EOF = '0' and high_shift_val_pst = "11")
                    ) then

                        high_shift_val_nst <= "11";
                        TX_MFB_EOF         <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));

                        if (RX_MFB_EOF = '0') then
                            TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(3, TX_MFB_EOF_POS'length));
                        else
                            TX_MFB_EOF_POS <= std_logic_vector(rx_mfb_eof_pos_u(TX_MFB_EOF_POS'high + 2 downto 2) + 4);
                        end if;
                    end if;

                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    TX_MFB_DATA    <= (TX_MFB_DATA'high downto 128 + 64 => '0') & HDRM_DMA_HDR_DATA & HDRM_DMA_PCIE_HDR;
                    TX_MFB_SOF     <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                    TX_MFB_EOF     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                    TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(5, TX_MFB_EOF_POS'length));

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_amd_2_rgn_g : if ((not IS_INTEL) and TX_REGIONS = 2) generate
        tprocess_nst_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'range);
        begin
            tprocess_nst     <= tprocess_pst;
            rx_mfb_eof_pos_u := unsigned(RX_MFB_EOF_POS);

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif ((not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) and HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                            -- The transaction spans multiple output words
                            if (RX_MFB_EOF = '0'
                                -- If the EOF_POS of the input is in this range, the second region
                                -- in the next beat is empty and can therefore fit the DMA header so
                                -- its PCIe header has to be ready as well as the DMA header itself.
                                or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 48 and rx_mfb_eof_pos_u < 80 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                                -- The EOF_POS greater than or equal to 80 means that the
                                -- transaction will span two words but the second region in the next
                                -- beat does not contain space for a DMA header.
                                or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 80 and rx_mfb_eof_pos_u < 112)
                                -- The transaction fits into three bus beats and, since we are
                                -- dispatching by 128 bytes, the second region in the third word is
                                -- always free which can fit the DMA header
                                or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 112 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                            ) then
                                tprocess_nst <= TRANSACTION_SEND;

                            -- The transaction fits in one word but spans over two regions, then next
                            -- beat will contain just the DMA header.
                            elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 16 and rx_mfb_eof_pos_u < 48) then
                                tprocess_nst <= DMA_HDR_SEND;

                                -- The transaction fits into one region and the second region contains
                                -- its DMA header
                                -- elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 16) then
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (TX_MFB_DST_RDY = '1') then
                        -- The transaction ends in the second beat so the next beat will contain just
                        -- the DMA header
                        if (RX_MFB_EOF = '1' and (rx_mfb_eof_pos_u >= 80 and rx_mfb_eof_pos_u < 112)) then
                            tprocess_nst <= DMA_HDR_SEND;

                        -- THe DMA header is sent in the second region of the third beat if either
                        -- packet does not end or if the packet EOF_POS is greater than or equal 112
                        elsif ((high_shift_val_pst = "11" and (RX_MFB_EOF = '0' or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 112)))
                            -- OR the DMA header fits in the second region of the current (i.e.
                            -- second) beat
                               or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 80)) then

                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                -- In case of 2 regions and for this state, always place the Header on the
                -- beginning of an output word.
                when DMA_HDR_SEND =>
                    if (TX_MFB_DST_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        -- For more description of a states, check the transition process, i.e. tprocess_nst_logic_p
        tshift_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'range);
        begin
            rx_mfb_eof_pos_u := unsigned(RX_MFB_EOF_POS);

            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    -- Valid data with their PCIe header
                    if (RX_MFB_SRC_RDY = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        -- If the current transaction fits into one word,
                        if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 16 and rx_mfb_eof_pos_u < 48) then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                        -- If the transaction fits into one regions, the second contains DMA header
                        -- so it itself and its PCIe header as to be ready on top of that
                        elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 16 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            HDRM_DMA_PCIE_HDR_DST_RDY  <= TX_MFB_DST_RDY;
                            HDRM_DMA_HDR_DST_RDY       <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_PKT_DROP = '1') then
                        RX_MFB_DST_RDY <= '1';
                        if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                            HDRM_DMA_HDR_DST_RDY <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (RX_MFB_EOF = '1' and (rx_mfb_eof_pos_u >= 80 and rx_mfb_eof_pos_u < 112)) then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                    elsif (high_shift_val_pst = "11" and RX_MFB_EOF = '0') then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                    elsif (high_shift_val_pst = "11" and RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 112) then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_PCIE_HDR_DST_RDY  <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY       <= TX_MFB_DST_RDY;

                    elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 80) then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_PCIE_HDR_DST_RDY  <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY       <= TX_MFB_DST_RDY;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY      <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= '1';

                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= '1';
                    end if;
            end case;
        end process;

        TX_MFB_EOF_POS        <= slv_array_ser(tx_mfb_eof_pos_arr);
        -- DMA header that as the only one can sometimes start in the second region has its FBE
        -- and LBE bits permanently tied to 1
        tx_mfb_meta_arr(1)    <= (PCIE_RQ_META_FBE => "1111", PCIE_RQ_META_LBE => "1111", others => '0');

        tout_logic_p : process (all) is
            variable rx_mfb_eof_pos_u   : unsigned(RX_MFB_EOF_POS'range);
            variable trans_byte_length  : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable data_pcie_hdr_corr : std_logic_vector(HDRM_DATA_PCIE_HDR'range);
        begin
            high_shift_val_nst <= high_shift_val_pst;

            tx_mfb_meta_arr(0)                   <= (others => '0');
            tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= (others => '1');
            tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= (others => '1');

            TX_MFB_DATA           <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF            <= (others => '0');
            TX_MFB_EOF            <= (others => '0');
            TX_MFB_SOF_POS        <= (others => '0');
            tx_mfb_eof_pos_arr(0) <= (others => '0');
            tx_mfb_eof_pos_arr(1) <= std_logic_vector(to_unsigned(5, maximum(1, log2(TX_REGION_SIZE*TX_BLOCK_SIZE))));
            TX_MFB_SRC_RDY        <= '0';

            rx_mfb_eof_pos_u   := unsigned(RX_MFB_EOF_POS);
            data_pcie_hdr_corr := HDRM_DATA_PCIE_HDR;
            trans_byte_length  := resize(rx_mfb_eof_pos_u, rx_mfb_eof_pos_u'length+1) + 1;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        -- Maybe this is obsolete since when the packet should be dropped, no
                        -- HDRM_DATA_PCIE_HDR_SRC_RDY will be valid anyways
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))
                    ) then
                        if (RX_MFB_EOF = '1') then
                            data_pcie_hdr_corr(A_RQ_HDR_DWORD_CNT) := std_logic_vector(resize(rx_mfb_eof_pos_u(rx_mfb_eof_pos_u'high downto 2), A_RQ_HDR_DWORD_CNT_W) + 1);

                            case trans_byte_length is
                                when to_unsigned(1, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0001";
                                when to_unsigned(2, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0011";
                                when to_unsigned(3, trans_byte_length'length) => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "0111";
                                when others                                   => tx_mfb_meta_arr(0)(PCIE_RQ_META_FBE) <= "1111";
                            end case;

                            if (trans_byte_length > 4) then
                                case trans_byte_length(1 downto 0) is
                                    when "00"   => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "1111";
                                    when "01"   => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0001";
                                    when "10"   => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0011";
                                    when "11"   => tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0111";
                                    when others => null;
                                end case;
                            else
                                tx_mfb_meta_arr(0)(PCIE_RQ_META_LBE) <= "0000";
                            end if;

                            if (rx_mfb_eof_pos_u < 16 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                                TX_MFB_DATA           <= (TX_MFB_DATA'high downto 128 + 64 + (TX_MFB_DATA'length / 2) => '0')
                                                         & HDRM_DMA_HDR_DATA
                                                         & HDRM_DMA_PCIE_HDR
                                                         & bshifter_data_out(TX_MFB_DATA'length/2 -1 downto 128)
                                                         & data_pcie_hdr_corr;
                                TX_MFB_SOF            <= "11";
                                TX_MFB_EOF            <= "11";
                                tx_mfb_eof_pos_arr(0) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);
                                TX_MFB_SRC_RDY        <= '1';

                            elsif (rx_mfb_eof_pos_u >= 16 and rx_mfb_eof_pos_u < 48) then
                                TX_MFB_DATA           <= bshifter_data_out(TX_MFB_DATA'high downto 128) & data_pcie_hdr_corr;
                                TX_MFB_SOF(0)         <= '1';
                                TX_MFB_EOF            <= "10";
                                tx_mfb_eof_pos_arr(1) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);
                                TX_MFB_SRC_RDY        <= '1';

                            elsif ((rx_mfb_eof_pos_u >= 48 and rx_mfb_eof_pos_u < 80 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                                   or (rx_mfb_eof_pos_u >= 80 and rx_mfb_eof_pos_u < 112)
                                   or (rx_mfb_eof_pos_u >= 112 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                               ) then
                                high_shift_val_nst <= init_shift;
                                TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 128) & data_pcie_hdr_corr;
                                TX_MFB_SOF(0)      <= '1';
                                TX_MFB_SRC_RDY     <= '1';
                            end if;
                        else
                            high_shift_val_nst <= init_shift;
                            TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 128) & HDRM_DATA_PCIE_HDR;
                            TX_MFB_SOF(0)      <= '1';
                            TX_MFB_SRC_RDY     <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 80) then
                        high_shift_val_nst    <= "11";
                        TX_MFB_DATA           <= (TX_MFB_DATA'high downto 128 + 64 + (TX_MFB_DATA'length / 2) => '0')
                                                 & HDRM_DMA_HDR_DATA
                                                 & HDRM_DMA_PCIE_HDR
                                                 & bshifter_data_out(TX_MFB_DATA'length/2 -1 downto 0);
                        TX_MFB_SOF            <= "10";
                        TX_MFB_EOF            <= "11";
                        tx_mfb_eof_pos_arr(0) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);
                        tx_mfb_eof_pos_arr(1) <= std_logic_vector(to_unsigned(5, TX_EOF_POS_RGN_LEN));

                    elsif (RX_MFB_EOF = '1' and (rx_mfb_eof_pos_u >= 80 and rx_mfb_eof_pos_u < 112)) then
                        high_shift_val_nst    <= "11";
                        TX_MFB_EOF            <= "10";
                        tx_mfb_eof_pos_arr(1) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);

                    elsif ((RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 112) and high_shift_val_pst = "11") then
                        high_shift_val_nst    <= high_shift_val_pst;
                        TX_MFB_DATA           <= (TX_MFB_DATA'high downto 128 + 64 + (TX_MFB_DATA'length / 2) => '0')
                                                 & HDRM_DMA_HDR_DATA
                                                 & HDRM_DMA_PCIE_HDR
                                                 & bshifter_data_out(TX_MFB_DATA'length/2 -1 downto 0);
                        TX_MFB_SOF            <= "10";
                        TX_MFB_EOF            <= "11";
                        tx_mfb_eof_pos_arr(0) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);
                        tx_mfb_eof_pos_arr(1) <= std_logic_vector(to_unsigned(5, TX_EOF_POS_RGN_LEN));

                    elsif (RX_MFB_EOF = '0' and high_shift_val_pst = "11") then
                        high_shift_val_nst    <= high_shift_val_pst;
                        TX_MFB_EOF            <= "01";
                        tx_mfb_eof_pos_arr(0) <= std_logic_vector(to_unsigned(3, TX_EOF_POS_RGN_LEN));
                    end if;

                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    TX_MFB_DATA           <= (TX_MFB_DATA'high downto 128 + 64 => '0') & HDRM_DMA_HDR_DATA & HDRM_DMA_PCIE_HDR;
                    TX_MFB_SOF            <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                    TX_MFB_EOF            <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                    tx_mfb_eof_pos_arr(0) <= std_logic_vector(to_unsigned(5, TX_EOF_POS_RGN_LEN));

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_intel_1_rgn_g : if (IS_INTEL and TX_REGIONS = 1) generate
        tprocess_nst_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'length +1 -1 downto 0);
        begin
            tprocess_nst     <= tprocess_pst;
            rx_mfb_eof_pos_u := resize(unsigned(RX_MFB_EOF_POS), RX_MFB_EOF_POS'length+1);

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif ((not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) and HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                            -- If the current input word does not fit into one output word, then
                            -- proceed normally.
                            if (RX_MFB_EOF = '0' or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 32)) then
                                tprocess_nst <= TRANSACTION_SEND;

                            -- If a current input word fits into one output one, then send a DMA
                            -- header in the next word.
                            else
                                tprocess_nst <= DMA_HDR_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (TX_MFB_DST_RDY = '1') then
                        if (RX_MFB_EOF = '1'
                            and ((resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32 > rx_mfb_eof_pos_u)
                        ) then

                            tprocess_nst <= DMA_HDR_SEND;

                        elsif (RX_MFB_EOF = '0' and high_shift_val_pst = "11") then
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    if (TX_MFB_DST_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
        begin
            rx_mfb_eof_pos_u := resize(unsigned(RX_MFB_EOF_POS), RX_MFB_EOF_POS'length+1);

            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        if (RX_MFB_EOF = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1' and rx_mfb_eof_pos_u < 32) then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_PKT_DROP = '1') then
                        RX_MFB_DST_RDY <= '1';

                        if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                            HDRM_DMA_HDR_DST_RDY <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (RX_MFB_EOF = '1'
                        and (((resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32) > rx_mfb_eof_pos_u)
                    ) then

                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;

                    elsif (RX_MFB_EOF = '0' and high_shift_val_pst = "11") then
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                    end if;

                when DMA_HDR_SEND =>

                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY      <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= '1';

                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= '1';
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
            variable rx_mfb_eof_pos_u   : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable trans_byte_length  : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable data_pcie_hdr_corr : std_logic_vector(HDRM_DATA_PCIE_HDR'range);
        begin
            high_shift_val_nst <= high_shift_val_pst;
            rx_mfb_eof_pos_u   := resize(unsigned(RX_MFB_EOF_POS), rx_mfb_eof_pos_u'length);

            tx_mfb_meta_arr                      <= (others => (others => '0'));

            TX_MFB_DATA    <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF     <= (others => '0');
            TX_MFB_EOF     <= (others => '0');
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= (others => '0');
            TX_MFB_SRC_RDY <= '0';

            data_pcie_hdr_corr := HDRM_DATA_PCIE_HDR;
            trans_byte_length  := resize(rx_mfb_eof_pos_u, rx_mfb_eof_pos_u'length) + 1;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        -- Correct the DW count in the header
                        if (RX_MFB_EOF = '1') then
                            data_pcie_hdr_corr(I_RQ_HDR_DW_CNT) := std_logic_vector(resize(rx_mfb_eof_pos_u(rx_mfb_eof_pos_u'high-1 downto 2), I_RQ_HDR_DW_CNT_W) + 1);

                            case trans_byte_length is
                                when to_unsigned(1, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0001";
                                when to_unsigned(2, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0011";
                                when to_unsigned(3, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0111";
                                when others                                   => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "1111";
                            end case;

                            if (trans_byte_length > 4) then
                                case trans_byte_length(1 downto 0) is
                                    when "00"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "1111";
                                    when "01"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0001";
                                    when "10"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0011";
                                    when "11"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0111";
                                    when others => null;
                                end case;
                            else
                                data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0000";
                            end if;
                        end if;

                        TX_MFB_DATA                             <= bshifter_data_out(TX_MFB_DATA'high downto 0);
                        tx_mfb_meta_arr(0)(PCIE_RQ_META_HEADER) <= data_pcie_hdr_corr;
                        TX_MFB_SOF                              <= "1";
                        TX_MFB_SRC_RDY                          <= '1';

                        if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 32) then
                            TX_MFB_EOF     <= "1";
                            -- The value is the EOF_POS in DWs (the RX_MFB_EOF_POS is in bytes)
                            -- derived from the RX_MFB_EOF_POS incremented by the size of the PCIe header.
                            TX_MFB_EOF_POS <= std_logic_vector(rx_mfb_eof_pos_u(TX_MFB_EOF_POS'high + 2 downto 2));
                        else
                            high_shift_val_nst <= init_shift;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if ((RX_MFB_EOF = '1'
                         and ((((resize(high_shift_val_pst, rx_mfb_eof_pos_u'length) + 1)*32) > rx_mfb_eof_pos_u)))
                        or (RX_MFB_EOF = '0' and high_shift_val_pst = "11")
                    ) then
                        high_shift_val_nst <= "11";
                        TX_MFB_EOF         <= "1";

                        if (RX_MFB_EOF = '0') then
                            TX_MFB_EOF_POS <= (others => '1');
                        else
                            TX_MFB_EOF_POS <= std_logic_vector(rx_mfb_eof_pos_u(TX_MFB_EOF_POS'high + 2 downto 2));
                        end if;
                    end if;

                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    TX_MFB_DATA                             <= (TX_MFB_DATA'high downto 64 => '0') & HDRM_DMA_HDR_DATA;
                    tx_mfb_meta_arr(0)(PCIE_RQ_META_HEADER) <= HDRM_DMA_PCIE_HDR;
                    TX_MFB_SOF                              <= "1";
                    TX_MFB_EOF                              <= "1";
                    TX_MFB_EOF_POS                          <= std_logic_vector(to_unsigned(1, TX_MFB_EOF_POS'length));

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_intel_2_rgn_g : if (IS_INTEL and TX_REGIONS = 2) generate
        tprocess_nst_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'range);
        begin
            tprocess_nst     <= tprocess_pst;
            rx_mfb_eof_pos_u := unsigned(RX_MFB_EOF_POS);

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and TX_MFB_DST_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif ((not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) and HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                            -- The transaction spans multiple output words
                            if (RX_MFB_EOF = '0'
                                -- If the EOF_POS of the input is in this range, the second region
                                -- in the next beat is empty and can therefore fit the DMA header so
                                -- its PCIe header has to be ready as well as the DMA header itself.
                                or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 64 and rx_mfb_eof_pos_u < 96 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                                -- The EOF_POS greater than or equal to 96 means that the
                                -- transaction will span two words but the second region in the next
                                -- beat does not contain space for a DMA header.
                                or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 96)
                            ) then
                                tprocess_nst <= TRANSACTION_SEND;

                            -- The transaction fits in one word but spans over two regions, then next
                            -- beat will contain just the DMA header.
                            elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 32 and rx_mfb_eof_pos_u < 64) then
                                tprocess_nst <= DMA_HDR_SEND;

                                -- The transaction fits into one region and the second region contains
                                -- its DMA header
                                -- elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 16) then
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>

                    if (TX_MFB_DST_RDY = '1') then
                        -- The transaction ends in the second second region so the next beat will contain just
                        -- the DMA header
                        if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 96) then
                            tprocess_nst <= DMA_HDR_SEND;

                        -- the DMA header fits in the second region of the current (i.e. second)
                        -- beat
                        elsif (RX_MFB_EOF = '0' or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 96)) then
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                -- In case of 2 regions and for this state, always place the Header on the
                -- beginning of an output word.
                when DMA_HDR_SEND =>
                    if (TX_MFB_DST_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        -- For more description of a states, check the transition process, i.e. tprocess_nst_logic_p
        tshift_logic_p : process (all) is
            variable rx_mfb_eof_pos_u : unsigned(RX_MFB_EOF_POS'range);
        begin
            rx_mfb_eof_pos_u := unsigned(RX_MFB_EOF_POS);

            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    -- Valid data with their PCIe header
                    if (RX_MFB_SRC_RDY = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then
                        -- If the current transaction fits into one word,
                        if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 32 and rx_mfb_eof_pos_u < 64) then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                        -- If the transaction fits into one regions, the second contains DMA header
                        -- so it itself and its PCIe header as to be ready on top of that
                        elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 32 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                            RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                            HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            HDRM_DMA_PCIE_HDR_DST_RDY  <= TX_MFB_DST_RDY;
                            HDRM_DMA_HDR_DST_RDY       <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_PKT_DROP = '1') then
                        RX_MFB_DST_RDY <= '1';
                        if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                            HDRM_DMA_HDR_DST_RDY <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (RX_MFB_EOF = '0' or (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 96)) then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                    elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 96) then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_PCIE_HDR_DST_RDY  <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY       <= TX_MFB_DST_RDY;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY      <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= '1';

                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= '1';
                    end if;
            end case;
        end process;

        TX_MFB_EOF_POS     <= slv_array_ser(tx_mfb_eof_pos_arr);
        -- DMA header that as the only one can sometimes start in the second region has its FBE
        -- and LBE bits permanently tied to 1
        tx_mfb_meta_arr(1) <= (PCIE_RQ_META_HEADER => HDRM_DMA_PCIE_HDR, others => '0');

        tout_logic_p : process (all) is
            variable rx_mfb_eof_pos_u   : unsigned(RX_MFB_EOF_POS'range);
            variable trans_byte_length  : unsigned(RX_MFB_EOF_POS'length+1 -1 downto 0);
            variable data_pcie_hdr_corr : std_logic_vector(HDRM_DATA_PCIE_HDR'range);
        begin
            high_shift_val_nst <= high_shift_val_pst;

            tx_mfb_meta_arr(0) <= (others => '0');

            TX_MFB_DATA           <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF            <= (others => '0');
            TX_MFB_EOF            <= (others => '0');
            TX_MFB_SOF_POS        <= (others => '0');
            tx_mfb_eof_pos_arr(0) <= (others => '0');
            tx_mfb_eof_pos_arr(1) <= std_logic_vector(to_unsigned(5, maximum(1, log2(TX_REGION_SIZE*TX_BLOCK_SIZE))));
            TX_MFB_SRC_RDY        <= '0';

            rx_mfb_eof_pos_u   := unsigned(RX_MFB_EOF_POS);
            data_pcie_hdr_corr := HDRM_DATA_PCIE_HDR;
            trans_byte_length  := resize(rx_mfb_eof_pos_u, rx_mfb_eof_pos_u'length+1) + 1;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1' and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        -- Maybe this is obsolete since when the packet should be dropped, no
                        -- HDRM_DATA_PCIE_HDR_SRC_RDY will be valid anyways
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))
                    ) then
                        if (RX_MFB_EOF = '1') then
                            data_pcie_hdr_corr(I_RQ_HDR_DW_CNT) := std_logic_vector(resize(rx_mfb_eof_pos_u(rx_mfb_eof_pos_u'high downto 2), I_RQ_HDR_DW_CNT_W) + 1);

                            case trans_byte_length is
                                when to_unsigned(1, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0001";
                                when to_unsigned(2, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0011";
                                when to_unsigned(3, trans_byte_length'length) => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "0111";
                                when others                                   => data_pcie_hdr_corr(I_RQ_HDR_FBE) := "1111";
                            end case;

                            if (trans_byte_length > 4) then
                                case trans_byte_length(1 downto 0) is
                                    when "00"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "1111";
                                    when "01"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0001";
                                    when "10"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0011";
                                    when "11"   => data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0111";
                                    when others => null;
                                end case;
                            else
                                data_pcie_hdr_corr(I_RQ_HDR_LBE) := "0000";
                            end if;

                            tx_mfb_meta_arr(0)(PCIE_RQ_META_HEADER) <= data_pcie_hdr_corr;

                            if (rx_mfb_eof_pos_u < 32 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                                TX_MFB_DATA           <= (TX_MFB_DATA'high downto 64 + (TX_MFB_DATA'length / 2) => '0')
                                                         & HDRM_DMA_HDR_DATA
                                                         & bshifter_data_out(TX_MFB_DATA'length/2 -1 downto 0);
                                TX_MFB_SOF            <= "11";
                                TX_MFB_EOF            <= "11";
                                tx_mfb_eof_pos_arr(0) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2));
                                TX_MFB_SRC_RDY        <= '1';

                            elsif (rx_mfb_eof_pos_u >= 32 and rx_mfb_eof_pos_u < 64) then
                                TX_MFB_SOF(0)         <= '1';
                                TX_MFB_EOF            <= "10";
                                tx_mfb_eof_pos_arr(1) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2) + 4);
                                TX_MFB_SRC_RDY        <= '1';

                            elsif ((rx_mfb_eof_pos_u >= 64 and rx_mfb_eof_pos_u < 96 and HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1')
                                   or rx_mfb_eof_pos_u >= 96
                               ) then
                                high_shift_val_nst <= init_shift;
                                TX_MFB_SOF(0)      <= '1';
                                TX_MFB_SRC_RDY     <= '1';
                            end if;
                        else
                            high_shift_val_nst                      <= init_shift;
                            tx_mfb_meta_arr(0)(PCIE_RQ_META_HEADER) <= HDRM_DATA_PCIE_HDR;
                            TX_MFB_SOF(0)                           <= '1';
                            TX_MFB_SRC_RDY                          <= '1';
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= "00";
                    TX_MFB_SRC_RDY     <= '1';

                    if (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u < 96) then
                        TX_MFB_DATA           <= (TX_MFB_DATA'high downto 64 + (TX_MFB_DATA'length / 2) => '0')
                                                 & HDRM_DMA_HDR_DATA
                                                 & bshifter_data_out(TX_MFB_DATA'length/2 -1 downto 0);
                        TX_MFB_SOF            <= "10";
                        TX_MFB_EOF            <= "11";
                        tx_mfb_eof_pos_arr(0) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2));
                        tx_mfb_eof_pos_arr(1) <= std_logic_vector(to_unsigned(1, TX_EOF_POS_RGN_LEN));

                    elsif (RX_MFB_EOF = '1' and rx_mfb_eof_pos_u >= 96) then
                        TX_MFB_EOF            <= "10";
                        tx_mfb_eof_pos_arr(1) <= std_logic_vector(rx_mfb_eof_pos_u(TX_EOF_POS_RGN_LEN-1 + 2 downto 2));

                    elsif (RX_MFB_EOF = '0') then
                        TX_MFB_EOF            <= "10";
                        tx_mfb_eof_pos_arr(1) <= (others => '1');
                    end if;

                when DMA_HDR_SEND =>
                    TX_MFB_DATA                             <= (TX_MFB_DATA'high downto 64 => '0') & HDRM_DMA_HDR_DATA;
                    tx_mfb_meta_arr(0)(PCIE_RQ_META_HEADER) <= HDRM_DMA_PCIE_HDR;
                    TX_MFB_SOF                              <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                    TX_MFB_EOF                              <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                    tx_mfb_eof_pos_arr(0)                   <= std_logic_vector(to_unsigned(1, TX_EOF_POS_RGN_LEN));

                    if (HDRM_DMA_HDR_SRC_RDY = '1' and HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    -- Same for Intel ... the reset value must change
    -- my attempt to make the set of constants which change according to the specified generic parameters
    shift_cntr_incr_g : if (TX_REGIONS = 1) generate
        init_shift <= "00";
        shift_inc  <= "01";
    else generate
        init_shift <= "01";
        -- increment by two, the barrel shifter remains the same for both of the configurations so the
        -- shifting by two is needed
        shift_inc  <= "10";
    end generate;

    --=============================================================================================================
    -- Shifter of the output data
    --=============================================================================================================
    input_data_shifter_i : entity work.BARREL_SHIFTER_GEN
    generic map (
        -- shift by 128b chunks (which is the size of PCIe header on AMD devices, on Intel, the
        -- shift gets more coarse since the PCIe header is transported in the meta signal of the
        -- output bus)
        BLOCKS     => 8,
        BLOCK_SIZE => 128,
        SHIFT_LEFT => FALSE
    )
    port map (
        DATA_IN  => RX_MFB_DATA,
        DATA_OUT => bshifter_data_out,
        SEL      => std_logic_vector(high_shift_val_pst) & low_shift_val
    );

    intel_lowbits: if (not IS_INTEL) generate
        low_shift_val <= '1';
    else generate
        low_shift_val <= '0';
    end generate;

    TX_MFB_META <= slv_array_ser(tx_mfb_meta_arr);
end architecture;
