-- uinstr_gen.vhd: uInstruction generator for CrossbarX
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
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity CROSSBARX_UINSTR_GEN is
generic(
    -- Number of input instructions per Instruction Stream
    INSTRS          : integer := 4;
    -- Buffer A size
    BUF_A_COLS      : integer := 512;
    -- max(BUF_A_TRUE_ROWS)
    BUF_A_ROWS      : integer := 4;
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
port(
    -- ====================
    -- Clock and Reset
    -- ====================

    CLK             : in  std_logic;
    RESET           : in  std_logic;

    -- ====================
    -- Input Instructions
    -- ====================

    INSTR_A_COL     : in  std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    INSTR_A_ITEM    : in  slv_array_t     (INSTRS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    INSTR_B_COL     : in  slv_array_t     (INSTRS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    INSTR_B_ITEM    : in  slv_array_t     (INSTRS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    INSTR_LEN       : in  slv_array_t     (INSTRS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS+1)-1 downto 0);
    INSTR_COLOR     : in  std_logic_vector(INSTRS-1 downto 0);
    INSTR_VLD       : in  std_logic_vector(INSTRS-1 downto 0);
    INSTR_SRC_RDY   : in  std_logic;

    -- ====================
    -- Output uInstructions
    -- ====================

    UINSTR_A_COL    : out slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_A_COLS)-1 downto 0);
    -- item within one row
    UINSTR_A_ITEM   : out slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    UINSTR_B_COL    : out slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    UINSTR_B_ITEM   : out slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    UINSTR_LEN      : out slv_array_t     (BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS+1)-1 downto 0);
    UINSTR_COLOR    : out std_logic_vector(BUF_A_ROWS-1 downto 0);
    UINSTR_VLD      : out std_logic_vector(BUF_A_ROWS-1 downto 0)
);
end entity;

architecture FULL of CROSSBARX_UINSTR_GEN is

    -- Instruction register 0
    signal reg0_instr_a_col   : std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    signal reg0_instr_a_sop   : u_array_t       (INSTRS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg0_instr_a_eop   : u_array_t       (INSTRS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg0_instr_b_col   : u_array_t       (INSTRS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg0_instr_b_item  : u_array_t       (INSTRS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg0_instr_len     : u_array_t       (INSTRS-1 downto 0)(log2(BUF_A_ROWS*ROW_ITEMS+1)-1 downto 0);
    signal reg0_instr_color   : std_logic_vector(INSTRS-1 downto 0);
    signal reg0_instr_vld     : std_logic_vector(INSTRS-1 downto 0);

    -- uInstruction register 1
    signal reg1_uinstr_a_col  : std_logic_vector(log2(BUF_A_COLS)-1 downto 0);
    signal reg1_uinstr_a_item : u_array_2d_t(INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS)-1 downto 0);
    signal reg1_uinstr_b_col  : u_array_2d_t(INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS)-1 downto 0);
    signal reg1_uinstr_b_item : u_array_2d_t(INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0)(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
    signal reg1_uinstr_len    : u_array_2d_t(INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0)(log2(ROW_ITEMS+1)-1 downto 0);
    signal reg1_uinstr_color  : slv_array_t (INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0);
    signal reg1_uinstr_vld    : slv_array_t (INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0);

    signal b_ptr_tmp_s     : u_array_2d_t(INSTRS-1 downto 0)(BUF_A_ROWS-1 downto 0)(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
begin

    -------------------------------------------------------------
    -- Instruction register 0
    -------------------------------------------------------------
    -- Calulating item spread of each Instruction.

    reg0_instr_pr : process (CLK)
    begin
        if (rising_edge(CLK)) then

            -- Saving input to registers
            reg0_instr_a_col <= INSTR_A_COL;
            for I in 0 to INSTRS-1 loop
                reg0_instr_b_col (I) <= unsigned(INSTR_B_COL (I));
                reg0_instr_b_item(I) <= unsigned(INSTR_B_ITEM(I));
                reg0_instr_len   (I) <= unsigned(INSTR_LEN   (I));
            end loop;
            reg0_instr_color <= INSTR_COLOR;
            reg0_instr_vld <= INSTR_VLD and INSTR_SRC_RDY;

            -- Calculate starting and ending item in buffer A column
            for I in 0 to INSTRS-1 loop
                reg0_instr_a_sop(I) <= unsigned(INSTR_A_ITEM(I));
                reg0_instr_a_eop(I) <= unsigned(INSTR_A_ITEM(I))+resize_left(unsigned(INSTR_LEN(I))-1,log2(BUF_A_ROWS*ROW_ITEMS));
            end loop;

            if (RESET='1') then
                reg0_instr_vld <= (others => '0');
            end if;
        end if;
    end process;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- uInstruction register 1
    -------------------------------------------------------------
    -- Generating a word of uInstructions for each Instruction.

    reg1_uinstr_pr : process (CLK)
        variable b_ptr_tmp      : unsigned(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto 0);
        variable b_ptr_orig_tmp : unsigned(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto 0);

        variable first_row : boolean;
        variable last_row  : boolean;
    begin
        if (rising_edge(CLK)) then

            -- Buffer A column is the same for all uInstructions
            reg1_uinstr_a_col  <= reg0_instr_a_col;

            for I in 0 to INSTRS-1 loop

                -- Setting default values to avoid latch
                reg1_uinstr_a_item(I) <= (others => (others => '0'));
                reg1_uinstr_b_col (I) <= (others => reg0_instr_b_col (I));
                reg1_uinstr_b_item(I) <= (others => reg0_instr_b_item(I));
                reg1_uinstr_len   (I) <= (others => resize_left(reg0_instr_len(I),log2(ROW_ITEMS+1)));
                reg1_uinstr_color (I) <= (others => reg0_instr_color (I));
                reg1_uinstr_vld   (I) <= (others => '0');

                -- Init loop variables
                b_ptr_tmp := (others => '0');

                for R in 0 to BUF_A_ROWS-1 loop

                    -- Detect first and last row
                    first_row := (R=resize_right(reg0_instr_a_sop(I),log2(BUF_A_ROWS)) or BUF_A_ROWS<2);
                    last_row  := (R=resize_right(reg0_instr_a_eop(I),log2(BUF_A_ROWS)) or BUF_A_ROWS<2);

                    -- Set valid
                    -- Valid are all rows from SOP to EOP
                    reg1_uinstr_vld(I)(R) <= reg0_instr_vld(I) when (R>=resize_right(reg0_instr_a_sop(I),log2(BUF_A_ROWS)) and R<=resize_right(reg0_instr_a_eop(I),log2(BUF_A_ROWS))) or BUF_A_ROWS<2 else '0';

                    -- Set buffer A item address
                    -- Only the first row can have an unaligned item address
                    reg1_uinstr_a_item(I)(R) <= (others => '0');
                    if (first_row) then
                        reg1_uinstr_a_item(I)(R) <= resize_left(reg0_instr_a_sop(I),log2(ROW_ITEMS));
                    end if;

                    ----
                    -- Calculate number of items for this row
                    -- Only the first and the last row of the uInstruction can have an unaligned number of items
                    reg1_uinstr_len(I)(R) <= to_unsigned(ROW_ITEMS,log2(ROW_ITEMS+1));

                    if (first_row and last_row) then -- the Instruction only describes one row in buffer A
                        reg1_uinstr_len(I)(R) <= resize_left(reg0_instr_len(I),log2(ROW_ITEMS+1));
                    elsif (first_row) then -- currently in the first row
                        reg1_uinstr_len(I)(R) <= to_unsigned(ROW_ITEMS,log2(ROW_ITEMS+1)) - resize_left(resize_left(reg0_instr_a_sop(I),log2(ROW_ITEMS)),log2(ROW_ITEMS+1));
                    elsif (last_row) then -- currently in the last row
                        reg1_uinstr_len(I)(R) <= enlarge_left(resize_left(reg0_instr_a_eop(I),log2(ROW_ITEMS)),1)+1;
                    end if;

                    ----

                    -- Calculate buffer B address
                    b_ptr_orig_tmp := reg0_instr_b_col(I) & reg0_instr_b_item(I);
                    b_ptr_tmp      := b_ptr_orig_tmp;
                    b_ptr_tmp      := b_ptr_tmp + resize_left(enlarge_right(to_unsigned(R,log2(BUF_A_ROWS+1)),log2(ROW_ITEMS)),b_ptr_tmp'length);
                    if (first_row) then
                        b_ptr_tmp      := b_ptr_tmp - resize_left(round_down(reg0_instr_a_sop(I),log2(ROW_ITEMS)),b_ptr_tmp'length);
                    else
                        b_ptr_tmp      := b_ptr_tmp - resize_left(reg0_instr_a_sop(I),b_ptr_tmp'length);
                    end if;
                    -- uInstruction must only overflow inside the Buffer B Section, where it begins
                    b_ptr_tmp(b_ptr_tmp'high downto b_ptr_tmp'high-log2(BUF_B_SECTIONS)+1) := b_ptr_orig_tmp(b_ptr_tmp'high downto b_ptr_tmp'high-log2(BUF_B_SECTIONS)+1);

                    -- Set buffer B address
                    reg1_uinstr_b_col (I)(R) <= b_ptr_tmp(log2(BUF_B_COLS*BUF_B_ROWS*ROW_ITEMS)-1 downto log2(BUF_B_ROWS*ROW_ITEMS));
                    reg1_uinstr_b_item(I)(R) <= b_ptr_tmp(log2(BUF_B_ROWS*ROW_ITEMS)-1 downto 0);

                    b_ptr_tmp_s(I)(R) <= b_ptr_tmp;

                end loop;

            end loop;

            if (RESET='1') then
                reg1_uinstr_vld <= (others => (others => '0'));
            end if;
        end if;
    end process;

    -------------------------------------------------------------

    -------------------------------------------------------------
    -- Output uInstruction register
    -------------------------------------------------------------
    -- Combining uInstructions from separate Instructions together

    output_uinstr_pr : process (CLK)
        -- debug checking variables
        variable v_uinstr_vld : std_logic_vector(BUF_A_ROWS-1 downto 0);
        variable v_uinstr_i   : i_array_t(BUF_A_ROWS-1 downto 0);
    begin
        if (rising_edge(CLK)) then

            for R in 0 to BUF_A_ROWS-1 loop

                -- Setting default values to avoid latch
                UINSTR_A_COL (R) <= reg1_uinstr_a_col;
                UINSTR_A_ITEM(R) <= std_logic_vector(reg1_uinstr_a_item(0)(R));
                UINSTR_B_COL (R) <= std_logic_vector(reg1_uinstr_b_col (0)(R));
                UINSTR_B_ITEM(R) <= std_logic_vector(reg1_uinstr_b_item(0)(R));
                UINSTR_LEN   (R) <= std_logic_vector(reg1_uinstr_len   (0)(R));
                UINSTR_COLOR (R) <=                  reg1_uinstr_color (0)(R);
                -- uInstruction is invalid until some Intruction covers it
                UINSTR_VLD   (R) <= '0';
                v_uinstr_vld (R) := '0';
                v_uinstr_i   (R) := 0;

                for I in 0 to INSTRS-1 loop

                    if (reg1_uinstr_vld(I)(R)='1') then

                        UINSTR_A_ITEM(R) <= std_logic_vector(reg1_uinstr_a_item(I)(R));
                        UINSTR_B_COL (R) <= std_logic_vector(reg1_uinstr_b_col (I)(R));
                        UINSTR_B_ITEM(R) <= std_logic_vector(reg1_uinstr_b_item(I)(R));
                        UINSTR_LEN   (R) <= std_logic_vector(reg1_uinstr_len   (I)(R));
                        UINSTR_COLOR (R) <=                  reg1_uinstr_color (I)(R);
                        UINSTR_VLD   (R) <= '1';

                        -- Check for Instruction overlapping
                        if (v_uinstr_vld(R)='1') then
                            report "ERROR: Uinstr Gen: Buffer A collision! Overlapping Instructions received!";
                            report "Instructions " & integer'image(v_uinstr_i(R)) &
                                   " and " & integer'image(I) &
                                   " both describe buffer A row " & integer'image(R) &
                                   "!";
                            report "" severity failure;
                        end if;
                        v_uinstr_vld(R) := '1';
                        v_uinstr_i  (R) := I;

                    end if;

                end loop;

            end loop;

            if (RESET='1') then
                UINSTR_VLD <= (others => '0');
            end if;
        end if;
    end process;

    -------------------------------------------------------------

end architecture;
