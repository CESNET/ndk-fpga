-- rx_dma_calypte_hdr_insertor.vhd: inserts PCIex header to each transfer and sends DMA header afterwards
-- Copyright (c) 2022 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-CLause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

-- Note:

use work.math_pack.all;
use work.type_pack.all;
use work.pcie_meta_pack.all;

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

    signal tx_mfb_meta_arr : slv_array_t(TX_REGIONS-1 downto 0)(PCIE_RQ_META_WIDTH-1 downto 0);

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

    --=============================================================================================================
    -- FSM state register
    --=============================================================================================================
    -- We still need shift data even though it's intel
    tprocess_pst_reg_p : process (CLK) is
    begin
        if (rising_edge(CLK)) then
            if (RST = '1') then

                tprocess_pst       <= IDLE;
                if (not IS_INTEL) then
                    high_shift_val_pst <= "11";
                else
                    high_shift_val_pst <= "00";
                end if;

            elsif (TX_MFB_DST_RDY = '1') then

                tprocess_pst       <= tprocess_nst;
                high_shift_val_pst <= high_shift_val_nst;
            end if;
        end if;
    end process;

    tprocess_amd_1_rgn_g : if (not IS_INTEL and TX_REGIONS = 1) generate
        tprocess_nst_logic_p : process (all) is
        begin
            tprocess_nst <= tprocess_pst;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        -- Don't wait for the DMA header if that does not arrive go forward.(it is
                        -- handled in a different place with its PCIe header)
                        elsif (HDRM_PKT_DROP = '0' or HDRM_DMA_HDR_SRC_RDY = '0') then
                            if (HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                                tprocess_nst <= TRANSACTION_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        -- the DMA header is sent in a separate word
                        if (RX_MFB_EOF = '1') then
                            tprocess_nst <= DMA_HDR_SEND;
                        elsif (RX_MFB_EOF = '0') then
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
        begin
            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                -- In this state, the component waits for the arrival of three crucial components,
                -- a valid packet, the PCIE header and the DMA header
                when IDLE =>
                    -- when valid word arrives deassert the RX_DST_RDY signal because the FSM awaits
                    -- the arrival of the PCIE header, no need to wait for the MFB_SOF signal the
                    -- RX_DST_RDY signal is sufficient
                    if (RX_MFB_SRC_RDY = '1') then
                        RX_MFB_DST_RDY <= '0';
                    end if;

                    -- awaiting the arrival of valid DMA header with the information if packet
                    -- should be dropped or not
                    if (HDRM_DMA_HDR_SRC_RDY = '1') then
                        -- when valid PKT_DROP signal is captured, then the next valid packet
                        -- should be dropped
                        if (HDRM_PKT_DROP = '1') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;

                            -- if valid SOF is captured, current DMA header is also dropped
                            if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                                HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        -- switch the PCIE header on the input to the next one DMA_HDR request
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                        if (RX_MFB_EOF = '0') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                -- This state will be used in One region configuration only
                when DMA_HDR_SEND =>
                    -- release the headers on the input and allow next packet to arrive
                    HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;

                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        RX_MFB_DST_RDY       <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= TX_MFB_DST_RDY;

                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
        begin
            high_shift_val_nst <= high_shift_val_pst;

            TX_MFB_DATA    <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF     <= (others => '0');
            TX_MFB_EOF     <= (others => '0');
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= (others => '0');
            TX_MFB_SRC_RDY <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))) then

                        high_shift_val_nst <= init_shift;
                        TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 128) & HDRM_DATA_PCIE_HDR;
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_SRC_RDY     <= '1';
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if (high_shift_val_pst = "11") then
                        high_shift_val_nst <= high_shift_val_pst;
                        TX_MFB_EOF         <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS     <= std_logic_vector(to_unsigned(3, TX_MFB_EOF_POS'length));
                    end if;
                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_DATA    <= (TX_MFB_DATA'high downto 128 + 64 => '0') & HDRM_DMA_HDR_DATA & HDRM_DMA_PCIE_HDR;
                        TX_MFB_SOF     <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_EOF     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(5, TX_MFB_EOF_POS'length));
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_amd_2_rgn_g : if (not IS_INTEL and TX_REGIONS = 2) generate
        tprocess_nst_logic_p : process (all) is
        begin
            tprocess_nst <= tprocess_pst;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif (HDRM_PKT_DROP = '0' or HDRM_DMA_HDR_SRC_RDY = '0') then
                            if (HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                                and ((HDRM_DMA_PCIE_HDR_SRC_RDY = '1'
                                         and RX_MFB_EOF = '1'
                                         and HDRM_DMA_HDR_SRC_RDY = '1')
                                        or RX_MFB_EOF = '0')) then

                                tprocess_nst <= TRANSACTION_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        tprocess_nst <= IDLE;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
        begin
            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        RX_MFB_DST_RDY <= '0';
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                            if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                                HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        RX_MFB_DST_RDY             <= TX_MFB_DST_RDY;
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        if (RX_MFB_EOF = '1') then
                            HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            HDRM_DMA_HDR_DST_RDY      <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        RX_MFB_DST_RDY       <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
        begin
            high_shift_val_nst <= high_shift_val_pst;

            TX_MFB_DATA    <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF     <= (others => '0');
            TX_MFB_EOF     <= (others => '0');
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= (others => '0');
            TX_MFB_SRC_RDY <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and (not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1'))
                        and ((HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '1')
                                or RX_MFB_EOF = '0')
                    ) then

                        high_shift_val_nst <= init_shift;
                        TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 128) & HDRM_DATA_PCIE_HDR;
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_SRC_RDY     <= '1';
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if (high_shift_val_pst = "11") then

                        high_shift_val_nst <= high_shift_val_pst;

                        if (RX_MFB_EOF = '1') then
                            TX_MFB_DATA    <= (TX_MFB_DATA'high downto 128 + 64 + (TX_MFB_DATA'length / 2) => '0')
                                              & HDRM_DMA_HDR_DATA
                                              & HDRM_DMA_PCIE_HDR
                                              & ((TX_MFB_DATA'length / 2) - 1 downto 128                   => '0')
                                              & bshifter_data_out(127 downto 0);
                            TX_MFB_SOF     <= std_logic_vector(to_unsigned(2, TX_MFB_SOF'length));
                            TX_MFB_EOF     <= std_logic_vector(to_unsigned(3, TX_MFB_EOF'length));
                            TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(43, TX_MFB_EOF_POS'length));
                        else
                            TX_MFB_EOF     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                            TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(3, TX_MFB_EOF_POS'length));
                        end if;
                    end if;

                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        TX_MFB_DATA    <= (TX_MFB_DATA'high downto 128 + 64 => '0') & HDRM_DMA_HDR_DATA & HDRM_DMA_PCIE_HDR;
                        TX_MFB_SOF     <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_EOF     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(5, TX_MFB_EOF_POS'length));
                        TX_MFB_SRC_RDY <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_intel_1_rgn_g : if (IS_INTEL and TX_REGIONS = 1) generate
        tprocess_nst_logic_p : process (all) is
        begin
            tprocess_nst <= tprocess_pst;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif (HDRM_PKT_DROP = '0' or HDRM_DMA_HDR_SRC_RDY = '0') then
                            if (HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                                tprocess_nst <= TRANSACTION_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        if (RX_MFB_EOF = '1') then
                            tprocess_nst <= DMA_HDR_SEND;
                        else
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
        begin
            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        RX_MFB_DST_RDY <= '0';
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                            if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                                HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "11") then
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        if (RX_MFB_EOF = '0') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        RX_MFB_DST_RDY       <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
        begin
            high_shift_val_nst <= high_shift_val_pst;

            TX_MFB_DATA    <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF     <= (others => '0');
            TX_MFB_EOF     <= (others => '0');
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= (others => '0');
            TX_MFB_SRC_RDY <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) then

                        high_shift_val_nst <= high_shift_val_pst + shift_inc;
                        TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 0);
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_SRC_RDY     <= '1';
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if (high_shift_val_pst = "11") then
                        TX_MFB_EOF     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(7, TX_MFB_EOF_POS'length));
                    end if;
                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        high_shift_val_nst <= (others                     => '0');
                        TX_MFB_DATA        <= (TX_MFB_DATA'high downto 64 => '0') & HDRM_DMA_HDR_DATA;
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_EOF         <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF_POS'length));
                        TX_MFB_SRC_RDY     <= '1';
                    end if;

                when PKT_DROP => null;
            end case;
        end process;
    end generate;

    tprocess_intel_2_rgn_g : if (IS_INTEL and TX_REGIONS = 2) generate
        tprocess_nst_logic_p : process (all) is
        begin
            tprocess_nst <= tprocess_pst;

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1' and RX_MFB_EOF = '0') then
                            tprocess_nst <= PKT_DROP;
                        elsif (HDRM_PKT_DROP = '0' or HDRM_DMA_HDR_SRC_RDY = '0') then
                            if (HDRM_DATA_PCIE_HDR_SRC_RDY = '1') then
                                tprocess_nst <= TRANSACTION_SEND;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "10") then
                        if (RX_MFB_EOF = '1') then
                            tprocess_nst <= DMA_HDR_SEND;
                        else
                            tprocess_nst <= IDLE;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;

                when PKT_DROP =>
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        tprocess_nst <= IDLE;
                    end if;
            end case;
        end process;

        tshift_logic_p : process (all) is
        begin
            RX_MFB_DST_RDY             <= '0';
            HDRM_DMA_PCIE_HDR_DST_RDY  <= '0';
            HDRM_DATA_PCIE_HDR_DST_RDY <= '0';
            HDRM_DMA_HDR_DST_RDY       <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1') then
                        RX_MFB_DST_RDY <= '0';
                    end if;

                    if (HDRM_DMA_HDR_SRC_RDY = '1') then
                        if (HDRM_PKT_DROP = '1') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                            if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                                HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                            end if;
                        end if;
                    end if;

                when TRANSACTION_SEND =>
                    if (high_shift_val_pst = "10") then
                        HDRM_DATA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                        if (RX_MFB_EOF = '0') then
                            RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                        end if;
                    end if;

                when DMA_HDR_SEND =>
                    HDRM_DMA_PCIE_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1' and HDRM_DMA_HDR_SRC_RDY = '1') then
                        RX_MFB_DST_RDY       <= TX_MFB_DST_RDY;
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;

                when PKT_DROP =>
                    RX_MFB_DST_RDY <= TX_MFB_DST_RDY;
                    if (RX_MFB_EOF = '1' and RX_MFB_SRC_RDY = '1') then
                        HDRM_DMA_HDR_DST_RDY <= TX_MFB_DST_RDY;
                    end if;
            end case;
        end process;

        tout_logic_p : process (all) is
        begin
            high_shift_val_nst <= high_shift_val_pst;

            TX_MFB_DATA    <= bshifter_data_out(TX_MFB_DATA'high downto 0);
            TX_MFB_SOF     <= (others => '0');
            TX_MFB_EOF     <= (others => '0');
            TX_MFB_SOF_POS <= (others => '0');
            TX_MFB_EOF_POS <= (others => '0');
            TX_MFB_SRC_RDY <= '0';

            case tprocess_pst is
                when IDLE =>
                    if (RX_MFB_SRC_RDY = '1'
                        and HDRM_DATA_PCIE_HDR_SRC_RDY = '1'
                        and not (HDRM_PKT_DROP = '1' and HDRM_DMA_HDR_SRC_RDY = '1')) then

                        high_shift_val_nst <= high_shift_val_pst + shift_inc;
                        TX_MFB_DATA        <= bshifter_data_out(TX_MFB_DATA'high downto 0);
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_SRC_RDY     <= '1';
                    end if;

                when TRANSACTION_SEND =>
                    high_shift_val_nst <= high_shift_val_pst + shift_inc;

                    if (high_shift_val_pst = "10") then
                        TX_MFB_EOF     <= std_logic_vector(to_unsigned(2, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS <= std_logic_vector(to_unsigned(56, TX_MFB_EOF_POS'length));
                    end if;
                    TX_MFB_SRC_RDY <= '1';

                when DMA_HDR_SEND =>
                    if (HDRM_DMA_PCIE_HDR_SRC_RDY = '1') then
                        high_shift_val_nst <= (others                     => '0');
                        TX_MFB_DATA        <= (TX_MFB_DATA'high downto 64 => '0') & HDRM_DMA_HDR_DATA;
                        TX_MFB_SOF         <= std_logic_vector(to_unsigned(1, TX_MFB_SOF'length));
                        TX_MFB_EOF         <= std_logic_vector(to_unsigned(1, TX_MFB_EOF'length));
                        TX_MFB_EOF_POS     <= std_logic_vector(to_unsigned(1, TX_MFB_EOF_POS'length));
                        TX_MFB_SRC_RDY     <= '1';
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
        -- 32 DWs and each has 32b
        BLOCKS     => 8,
        BLOCK_SIZE => 128,
        SHIFT_LEFT => FALSE
    )
    port map (
        DATA_IN  => RX_MFB_DATA,
        DATA_OUT => bshifter_data_out,
        SEL      => std_logic_vector(high_shift_val_pst) & low_shift_val
    );

    -- In intel devices the PCIe header is sent in separate signal.
    intel_lowbits: if (IS_INTEL = FALSE) generate
        low_shift_val <= '1';

        tx_mfb_meta_g: for i in 0 to TX_REGIONS-1 generate
            process (all) is
            begin
                tx_mfb_meta_arr(i)                   <= (others => '0');
                -- FBE and LBE for Xilinx FPGA
                tx_mfb_meta_arr(i)(PCIE_RQ_META_FBE) <= (others => '1');
                tx_mfb_meta_arr(i)(PCIE_RQ_META_LBE) <= (others => '1');
            end process;
        end generate;
    else generate
        low_shift_val   <= '0';

        tx_mfb_meta_g: for i in 0 to TX_REGIONS-1 generate
            process (all) is
            begin
                tx_mfb_meta_arr(i) <= (others => '0');

                if (tprocess_pst = DMA_HDR_SEND) then
                    tx_mfb_meta_arr(i)(PCIE_RQ_META_HEADER) <= HDRM_DMA_PCIE_HDR;
                else
                    tx_mfb_meta_arr(i)(PCIE_RQ_META_HEADER) <= HDRM_DATA_PCIE_HDR;
                end if;
            end process;
        end generate;
    end generate;

    TX_MFB_META <= slv_array_ser(tx_mfb_meta_arr);
end architecture;
