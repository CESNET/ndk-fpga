-- uinstr_splitter.vhd: uInstruction Splitter for CrossbarX
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                               Description
-- ----------------------------------------------------------------------------
-- Changes format of an uninstruction from Uinstr Gen format to Crossbar format.
-- The uInstruction describes data in one block in buffer A.
-- If the uInstruction is unaligned (takes data from 2 blocks in buffer B),
-- the Uinstr Splitter splits it in two with different SRC_ROW and DST_BE.
-- This effectively lowers the throughput to half, but it only happens,
-- when unaligned instructions are present on packet DMA (DMA_TYPE 3).

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_UINSTR_SPLITTER is
generic (
    -- Data transfer direction
    -- false -> from A to B
    -- true  -> from B to A
    DATA_DIR        : boolean := true;

    -- Number of input instructions per Instruction Stream
    INSTRS          : integer := 4;
    -- Buffer A size
    BUF_A_COLS      : integer := 512;
    -- Buffer B size
    BUF_B_COLS      : integer := 512;
    -- max(BUF_B_TRUE_ROWS)
    BUF_B_ROWS      : integer := 4;

    -- Number of non-overlapping Sections of Buffer B
    -- (All Instructions must overflow inside space
    --  of one Buffer B Section.)
    BUF_B_SECTIONS  : integer := 1;

    -- Number of items in one bufer row
    ROW_ITEMS       : integer := 8;
    -- Width of one item
    ITEM_WIDTH      : integer := 8;

    -- Target Device
    -- "ULTRASCALE", "7SERIES", ...
    DEVICE          : string := "STRATIX10"
);
port (
    -- ====================
    -- Clock and Reset
    -- ====================

    CLK                : in  std_logic;
    RESET              : in  std_logic;

    -- ====================
    -- Input uInstructions
    -- ====================

    RX_UINSTR_A_COL    : in  std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    -- item within one row
    RX_UINSTR_A_ITEM   : in  std_logic_vector(log2(ROW_ITEMS)-1 downto 0);
    RX_UINSTR_B_COL    : in  std_logic_vector(log2(BUF_B_COLS)-1 downto 0);
    RX_UINSTR_B_ITEM   : in  std_logic_vector(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    RX_UINSTR_LEN      : in  std_logic_vector(log2(ROW_ITEMS+1)-1 downto 0);
    RX_UINSTR_COLOR    : in  std_logic;
    RX_UINSTR_SRC_RDY  : in  std_logic;
    RX_UINSTR_DST_RDY  : out std_logic;

    -- ====================
    -- Output uInstructions
    -- ====================

    TX_UINSTR_A_COL    : out std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    TX_UINSTR_B_COL    : out std_logic_vector(log2(BUF_B_COLS)-1 downto 0);
    TX_UINSTR_B_ROW    : out std_logic_vector(log2(BUF_B_ROWS)-1 downto 0);
    -- row rotation
    TX_UINSTR_ROW_ROT  : out std_logic_vector(log2(ROW_ITEMS)-1 downto 0);
    -- item enable
    TX_UINSTR_IE       : out std_logic_vector(ROW_ITEMS-1 downto 0);
    TX_UINSTR_COLOR    : out std_logic;
    TX_UINSTR_SRC_RDY  : out std_logic;
    TX_UINSTR_DST_RDY  : in  std_logic
);
end entity;

architecture FULL of CROSSBARX_UINSTR_SPLITTER is

    -----------------------------------------------------------------------
    -- RX preprocessing
    -----------------------------------------------------------------------

    signal rx_uinstr_b_first_row_item       : unsigned(log2(2*ROW_ITEMS)-1 downto 0);
    signal rx_uinstr_b_last_row_item        : unsigned(log2(2*ROW_ITEMS)-1 downto 0);
    signal rx_uinstr_b_bitmap               : std_logic_vector(2*ROW_ITEMS-1 downto 0);
    signal rx_uinstr_a2b_shift              : unsigned(log2(ROW_ITEMS)-1 downto 0);
    signal rx_uinstr_b2a_shift              : unsigned(log2(ROW_ITEMS)-1 downto 0);
    signal rx_uinstr_b_last_item            : unsigned(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto 0);

    signal first_ie : std_logic_vector(ROW_ITEMS-1 downto 0);
    signal last_ie  : std_logic_vector(ROW_ITEMS-1 downto 0);

    -----------------------------------------------------------------------
    -- Control logic
    -----------------------------------------------------------------------

    signal current_step_reg : std_logic;
    signal next_step        : std_logic;

    -----------------------------------------------------------------------

begin

    -----------------------------------------------------------------------
    -- RX preprocessing
    -----------------------------------------------------------------------

    -- Item address of the first item in buffer B within the space of the 2 rows, that the uInstruction possibly describes.
    rx_uinstr_b_first_row_item <= enlarge_left(resize(unsigned(RX_UINSTR_B_ITEM),log2(ROW_ITEMS)),1);
    -- Item address of the last item in the uInstruction in buffer B within the space of the 2 rows,
    -- that the uInstruction possibly describes. This value cannot overflow after these two rows,
    -- since in the worst case the uInstruction can start at the last item of the first row and be ROW_ITEMS long.
    rx_uinstr_b_last_row_item  <= rx_uinstr_b_first_row_item + unsigned(RX_UINSTR_LEN) - 1;

    -- Valid bits for 2 rows in buffer B, that the uInstruction possibly describes.
    rx_uinstr_pre_pr : process (rx_uinstr_b_first_row_item,rx_uinstr_b_last_row_item)
    begin
        rx_uinstr_b_bitmap <= (others => '0');
        for i in 0 to ROW_ITEMS*2-1 loop
            if (i>=rx_uinstr_b_first_row_item and i<=rx_uinstr_b_last_row_item) then
                -- item is within uInstruction space boundaries
                rx_uinstr_b_bitmap(i) <= '1';
            end if;
        end loop;
    end process;

    -- difference from buffer B item offset to buffer A item offset in block
    rx_uinstr_a2b_shift <= resize(unsigned(RX_UINSTR_B_ITEM),log2(ROW_ITEMS)) - resize(unsigned(RX_UINSTR_A_ITEM),log2(ROW_ITEMS));
    rx_uinstr_b2a_shift <= resize(unsigned(RX_UINSTR_A_ITEM),log2(ROW_ITEMS)) - resize(unsigned(RX_UINSTR_B_ITEM),log2(ROW_ITEMS));

    -- Buffer B address of last item of the uInstruction
    rx_uinstr_b_last_item <= (unsigned(RX_UINSTR_B_COL) & unsigned(RX_UINSTR_B_ITEM))
                            +resize(unsigned(RX_UINSTR_LEN),log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS))
                            -1;

    -----------------------------------------------------------------------

    -----------------------------------------------------------------------
    -- Control logic
    -----------------------------------------------------------------------

    -- step 0 -> transforming the whole uInstruction or its first part
    -- step 1 -> transforming the second part of the uInstruction (not always needed)
    current_step_reg_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then
            if (ROW_ITEMS>1) then -- uInstructions are only being split when there are multiple Items in Buffer Row
                if (RX_UINSTR_SRC_RDY='1' and TX_UINSTR_DST_RDY='1') then
                    current_step_reg <= next_step;
                end if;
            end if;

            if (RESET='1') then
                current_step_reg <= '0';
            end if;
        end if;
    end process;

    --           '1' when (not already in step 1) and (uInstruction ends in different data block then where it begins) else '0';
    next_step <= '1' when (current_step_reg/='1') and (      rx_uinstr_b_last_row_item(log2(2*ROW_ITEMS)-1)='1'      ) else '0';

    -- read RX when output FIFOX is ready and we won't be processing this uInstruction any more
    RX_UINSTR_DST_RDY <= '1' when TX_UINSTR_DST_RDY='1' and (next_step='0' or RX_UINSTR_SRC_RDY='0') else '0';

    -----------------------------------------------------------------------

    -----------------------------------------------------------------------
    -- TX uinstrs generation
    -----------------------------------------------------------------------

    -- precomputing item enables
    first_last_ie_pr : process (rx_uinstr_b_bitmap,rx_uinstr_a2b_shift)
        variable v_first_ie : std_logic_vector(ROW_ITEMS-1 downto 0);
        variable v_last_ie  : std_logic_vector(ROW_ITEMS-1 downto 0);
    begin
        (v_last_ie,v_first_ie) := rx_uinstr_b_bitmap;
        first_ie <= v_first_ie;
        last_ie  <= v_last_ie;
        -- rotating item enables if transfering data from B to A
        if (DATA_DIR=false) then
            -- This rotation is avoided in case which does not work in Quartus
            if (ROW_ITEMS>1) then
                first_ie <= (v_first_ie ror to_integer(rx_uinstr_a2b_shift));
                last_ie  <= (v_last_ie  ror to_integer(rx_uinstr_a2b_shift));
            end if;
        end if;
    end process;

    -- output register
    tx_uinstr_pr : process (CLK)
        variable tmp_b_col : std_logic_vector(log2(BUF_B_COLS)-1 downto 0);
        variable tmp_b_row : std_logic_vector(log2(BUF_B_ROWS)-1 downto 0);
    begin
        if (rising_edge(CLK)) then
            -- only update the register, when TX is ready or not currently valid
            if (TX_UINSTR_DST_RDY='1' or TX_UINSTR_SRC_RDY='0') then
                -- write all valid uInstructions
                TX_UINSTR_SRC_RDY <= RX_UINSTR_SRC_RDY;

                -----------------
                -- some values are the same for both steps

                -- data block rotation is determined by the distance from buffer B item offset and buffer A item offset in row
                -- it depends on the direction of planning
                TX_UINSTR_ROW_ROT <= std_logic_vector(rx_uinstr_a2b_shift) when DATA_DIR=true else std_logic_vector(rx_uinstr_b2a_shift);
                -- a_col and color are just propagated
                TX_UINSTR_A_COL   <= RX_UINSTR_A_COL;
                TX_UINSTR_COLOR   <= RX_UINSTR_COLOR;

                -----------------

                -----------------
                -- some values are specific according to the current step

                if (current_step_reg='0') then

                    -- Use the same address as the RX uInstruction
                    TX_UINSTR_B_COL <= RX_UINSTR_B_COL;
                    TX_UINSTR_B_ROW <= std_logic_vector(enlarge_right(unsigned(RX_UINSTR_B_ITEM),-log2(ROW_ITEMS)));

                    -- a_ie is determined by the address of the valid items in the first row in buffer B
                    TX_UINSTR_IE <= first_ie;

                else

                    -- Use the computed address of the last item of the uInstruction
                    (tmp_b_col,
                     tmp_b_row ) := std_logic_vector(enlarge_right(rx_uinstr_b_last_item,-log2(ROW_ITEMS)));

                    -- Buffer B Column must overflow within space of one Buffer B Section
                    tmp_b_col(log2(BUF_B_COLS)-1 downto log2(BUF_B_COLS)-1-log2(BUF_B_SECTIONS)+1) := RX_UINSTR_B_COL(log2(BUF_B_COLS)-1 downto log2(BUF_B_COLS)-1-log2(BUF_B_SECTIONS)+1);
                    TX_UINSTR_B_COL <= tmp_b_col;
                    TX_UINSTR_B_ROW <= tmp_b_row;

                    -- a_ie is determined by the address of the valid items in the last row in buffer B
                    TX_UINSTR_IE <= last_ie;

                end if;

                -----------------

            end if;

            if (RESET='1') then
                TX_UINSTR_SRC_RDY <= '0';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------------

end architecture;
