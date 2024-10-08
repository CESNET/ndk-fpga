-- block_shifter.vhd : Block shifter to remove or insert a block of data from
--                     the stream
-- Copyright (C) 2012-2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--
-- TODO: The insert/drop operation is not allowed in some border cases: the
--       drop is not executed when shift=7 and IDX=7, and the insertion is
--       not executed when shift=0 and IDX=7

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity block_shifter is
    generic (
        NUM_LANES : natural := 8
    );
    port (
        RESET : in std_logic;
        CLK   : in std_logic;
        D     : in std_logic_vector(NUM_LANES*66-1 downto 0);  -- Input data
        D_VAL : in std_logic := '1';
        RE    : out std_logic; -- D read enable
        DROP  : in std_logic; -- Drop 1 data block
        INS   : in std_logic; -- Insert 1 data block
        IDX   : in natural range 0 to NUM_LANES-1; -- Index - block # to be dropped or inserted (insert before this block)
        --
        Q_VAL : out std_logic; -- Q valid
        Q     : out std_logic_vector(NUM_LANES*66-1 downto 0)  -- Output data
    );
end block_shifter;

architecture behavioral of block_shifter is

    type t_block_array is array (natural range <>) of std_logic_vector(65 downto 0);

    constant GBASER_IDLE : std_logic_vector(65 downto 0) := X"000000000000001E" & "01";
    constant EMPTY_BLOCK : t_block_array(0 downto 0) := (0=>GBASER_IDLE); -- 10GBASE-R IDLE block

    signal rin         : std_logic_vector(NUM_LANES*66-1 downto 0);
    signal din         : t_block_array(2*NUM_LANES-1 downto 0);
    signal data_window : t_block_array(NUM_LANES-1 downto 0);
    signal next_block  : t_block_array(0 downto 0);
    signal dropped_data: t_block_array(NUM_LANES-1 downto 0);
    signal inserted_data : t_block_array(NUM_LANES-1 downto 0);
    signal dout        : t_block_array(NUM_LANES-1 downto 0);
    signal shift       : natural range 0 to NUM_LANES-1 := 0;
    signal shift_r     : natural range 0 to NUM_LANES-1 := 0;
    signal index       : natural range 0 to NUM_LANES-1;
    signal drop_i      : std_logic;
    signal drop_r      : std_logic := '0';
    signal ins_i       : std_logic;
    signal ins_r       : std_logic := '0';
    signal idx_r       : natural range 0 to NUM_LANES-1 := 0;
    signal skip        : std_logic := '0';
    signal re_i        : std_logic;
    signal op_allow    : std_logic;

begin

    INPUT_REG: process(CLK)
    begin
        if CLK'event and CLK = '1' then
            if (re_i = '1') and (D_VAL = '1') then
                rin     <= D;
                ins_r   <= INS;
                drop_r  <= DROP;
                idx_r   <= IDX;
                shift_r <= shift;
            elsif D_VAL = '1' then
                ins_r   <= '0';
                drop_r  <= '0';
            end if;
        end if;
    end process;

    -- if (shift <= index) then the block will dropped in the next clock
    -- cycle, otherwise it will be dropped now
    SHIFT_CONTROL_LOGIC: process(DROP, INS, drop_r, ins_r, IDX, idx_r, shift, shift_r, re_i)
    begin
        drop_i <= '0';
        ins_i  <= '0';
        index  <= 0; -- idx_r - shift;
        if (IDX < shift) and ((DROP = '1') or (INS = '1')) then -- Insert/drop imedietaly
            drop_i <= DROP;
            ins_i  <= INS;
            index  <= NUM_LANES + IDX - shift;
        elsif (idx_r >= shift) then   -- Insert/drop in the second cycle
            ins_i  <= ins_r;
            drop_i <= drop_r;
            index  <= (NUM_LANES + idx_r - shift) mod NUM_LANES;
        end if;
    end process;

    -- Convert input data into blocks
    GEN_BLOCKS: for i in 0 to NUM_LANES-1 generate
        din(i) <= rin((i+1)*66-1 downto i*66);
        din(NUM_LANES+i) <= D((i+1)*66-1 downto i*66);
    end generate;

    -- data_window  <= din(shift + NUM_LANES - 1 downto shift); -- syntax not valid in Vivado:(
    GEN_WINDOW: for i in 0 to NUM_LANES - 1 generate
        data_window(i) <= din(shift + i);
    end generate;

    GEN_NB: for i in 0 to 0 generate
        next_block(i)   <= din(shift+NUM_LANES); -- next data block to be inserted when droping
    end generate;

    -- Syntax not valid in Vivado: dropped_data <= next_block & data_window(NUM_LANES-1 downto index+1) & data_window(index-1 downto 0);
    GEN_DD: for i in 0 to NUM_LANES-2 generate
        dropped_data(i) <= data_window(i) when (i < index) else
                           data_window(i+1);
    end generate;
    dropped_data(NUM_LANES-1) <= next_block(0);

    -- Syntax not valid in Vivado: inserted_data <= data_window(NUM_LANES-2 downto index) & EMPTY_BLOCK & data_window(index-1 downto 0);
    GEN_ID: for i in 1 to NUM_LANES-1 generate
        inserted_data(i) <= EMPTY_BLOCK(0) when (i = index) else
                            data_window(i) when (i < index) else
                            data_window(i-1);
    end generate;
    inserted_data(0) <= EMPTY_BLOCK(0) when (index = 0) else data_window(0);

    OUTPUT_MX_REG: process(CLK)
    begin
        if CLK'event and CLK = '1' then
            if D_VAL = '1' then
                skip  <= '0';
                if drop_i = '1' then
                    dout <= dropped_data;
                    if (shift = (NUM_LANES-1)) and (skip = '0') then
                        skip  <= '1';
                        shift <= 0;
                    elsif (skip = '0') then
                        shift <= shift + 1;
                    end if;
                elsif (ins_i = '1') then
                    dout <= inserted_data;
                    if (shift = 0) then
                        shift <= NUM_LANES-1;
                    else
                        shift <= shift - 1;
                    end if;
                else
                    dout <= data_window;
                end if;
            end if;

            Q_VAL <= (not skip) and D_VAL;
            if RESET = '1' then
                shift <= 0;
                skip  <= '0';
                Q_VAL <= '0';
            end if;
        end if;
    end process;

    re_i <= '0' when (ins_i = '1') and (shift = 0) else '1';

    -- Convert t_block_array to std_logic_vector
    DEBLOCK: for i in 0 to NUM_LANES-1 generate
        Q((i+1)*66-1 downto i*66) <= dout(i);
    end generate;

    RE <= re_i;

end behavioral;
