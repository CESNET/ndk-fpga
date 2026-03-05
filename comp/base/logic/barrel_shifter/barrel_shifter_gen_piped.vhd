-- barrel_shifter_gen.vhd: Barrel shifter with generic data width, generic block size and optional pipelining and output register
-- Copyright (C) 2026 CESNET
-- Author(s): Radek Iša <isa@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                  ENTITY DECLARATION -- Barrel shifter                     --
-- ----------------------------------------------------------------------------

entity BARREL_SHIFTER_GEN_PIPED is
    generic (
        -- input/output data width in BLOCKs
        BLOCKS       : integer := 256;
        -- width of one block in bits
        BLOCK_WIDTH  : integer := 64;
        -- NOTE: data_width = blocks*block_size

        -- barrel shifting latency
        BAR_SHIFT_LATENCY : integer := 0;
        -- input register enable (adds additional 1 CLK latency)
        INPUT_REG         : boolean := false;
        -- output register enable (adds additional 1 CLK latency)
        OUTPUT_REG        : boolean := false;

        -- set true to shift left, false to shift right
        SHIFT_LEFT  : boolean := false;

        -- Metadata can be useful when you want to send additional info to the TX side
        -- along with the rotated value. (for example the value of the RX_SEL signal)
        METADATA_WIDTH : integer := 0
    );
    port (
        CLK         : in  std_logic := '0'; -- unused when MUX_LATENCY==0 and OUTPUT_REG==INPUT_REG==false
        RESET       : in  std_logic := '0'; -- unused when MUX_LATENCY==0 and OUTPUT_REG==INPUT_REG==false

        RX_DATA     : in  std_logic_vector(BLOCK_WIDTH*BLOCKS-1 downto 0);
        RX_SEL      : in  std_logic_vector(log2(BLOCKS)-1 downto 0);
        RX_METADATA : in  std_logic_vector(METADATA_WIDTH-1 downto 0) := (others => '0');
        RX_SRC_RDY  : in  std_logic := '1';
        RX_DST_RDY  : out std_logic;

        TX_DATA     : out std_logic_vector(BLOCK_WIDTH*BLOCKS-1 downto 0);
        TX_METADATA : out std_logic_vector(METADATA_WIDTH-1 downto 0);
        TX_SRC_RDY  : out std_logic;
        TX_DST_RDY  : in  std_logic := '1'
    );
end entity;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture FULL of BARREL_SHIFTER_GEN_PIPED is
    constant DATA_WIDTH : natural := BLOCKS*BLOCK_WIDTH;

    -- INPUT STAGE
    signal r0_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal r0_sel      : std_logic_vector(log2(BLOCKS)-1 downto 0);
    signal r0_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal r0_src_rdy  : std_logic;
    signal r0_dst_rdy  : std_logic;

    signal r1_data_in  : unsigned(2*DATA_WIDTH-1 downto 0);
    signal r1_data_rot : unsigned(2*DATA_WIDTH-1 downto 0);
    signal r1_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal r1_sel      : integer range 0 to maximum(BLOCKS,0)-1; -- Don't change it. It would requires more resources.
    signal r1_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal r1_src_rdy  : std_logic;
    signal r1_dst_rdy  : std_logic;

    signal r2_data     : slv_array_t(BAR_SHIFT_LATENCY downto 0)(DATA_WIDTH-1 downto 0);
    signal r2_metadata : slv_array_t(BAR_SHIFT_LATENCY downto 0)(METADATA_WIDTH-1 downto 0);
    signal r2_src_rdy  : std_logic_vector(BAR_SHIFT_LATENCY downto 0);
    signal r2_dst_rdy  : std_logic_vector(BAR_SHIFT_LATENCY downto 0);

    signal r3_data     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal r3_metadata : std_logic_vector(METADATA_WIDTH-1 downto 0);
    signal r3_src_rdy  : std_logic;
    signal r3_dst_rdy  : std_logic;

begin

    -------------------------------------------------
    -- R0 STAGE
    -------------------------------------------------
    input_reg_gen : if (INPUT_REG) generate
        signal  rdy : std_logic;
    begin

        -- set  DST_RDY when previous pipeline is ready or this
        -- stage is empty
        rdy        <= '1' when r0_src_rdy = '0' or r0_dst_rdy = '1' else '0';
        RX_DST_RDY <= rdy;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if (RESET = '1') then
                    r0_src_rdy  <= '0';
                elsif (rdy = '1') then
                    r0_src_rdy  <= RX_SRC_RDY;
                end if;

                if (rdy = '1') then
                    r0_data     <= RX_DATA;
                    r0_sel      <= RX_SEL;
                    r0_metadata <= RX_METADATA;
                end if;
            end if;
        end process;
    else generate
        r0_data     <= RX_DATA;
        r0_sel      <= RX_SEL;
        r0_metadata <= RX_METADATA;
        r0_src_rdy  <= RX_SRC_RDY;
        RX_DST_RDY  <= r0_dst_rdy;
    end generate;

    -------------------------------------------------
    -- R1 STAGE - ROTATION
    -------------------------------------------------
    r1_metadata <= r0_metadata;
    r1_data_in  <= unsigned(r0_data) & unsigned(r0_data);
    r1_src_rdy  <= r0_src_rdy;
    r0_dst_rdy  <= r1_dst_rdy;

    sel_int_gen : if (BLOCKS > 1) generate
        r1_sel <= to_integer(unsigned(r0_sel)) when unsigned(r0_sel) < BLOCKS else
                  to_integer(unsigned'(log2(BLOCKS)-1 downto 0 => 'X'));
    else generate
        r1_sel <= 0;
    end generate;

    shift_sel_gen : if (SHIFT_LEFT) generate
        r1_data_rot <= IEEE.numeric_std.shift_left(r1_data_in, r1_sel*BLOCK_WIDTH);
        r1_data     <= std_logic_vector(r1_data_rot(DATA_WIDTH*2-1 downto DATA_WIDTH));
    else generate
        r1_data_rot <= IEEE.numeric_std.shift_right(r1_data_in, r1_sel*BLOCK_WIDTH);
        r1_data     <= std_logic_vector(r1_data_rot(DATA_WIDTH-1 downto 0));
    end generate;


    -------------------------------------------------
    -- R2 PIPELINE
    -------------------------------------------------
    r2_data(0)     <= r1_data;
    r2_metadata(0) <= r1_metadata;
    r2_src_rdy(0)  <= r1_src_rdy;
    r1_dst_rdy     <= r2_dst_rdy(0);

    pipeline_gen : for it in 0 to BAR_SHIFT_LATENCY-1 generate
        signal  rdy : std_logic;
    begin

        -- set  DST_RDY when previous pipeline is ready or this
        -- stage is empty
        rdy            <= '1' when r2_src_rdy(it+1) = '0' or r2_dst_rdy(it+1) = '1' else '0';
        r2_dst_rdy(it) <= rdy;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if (RESET = '1') then
                    r2_src_rdy(it+1)  <= '0';
                elsif (rdy = '1') then
                    r2_src_rdy(it+1) <= r2_src_rdy(it);
                end if;

                if (rdy = '1') then
                    r2_data(it+1)     <= r2_data(it);
                    r2_metadata(it+1) <= r2_metadata(it);
                end if;
            end if;
        end process;
    end generate;

    -------------------------------------------------
    -- R3 OUTPUT REG/ OUTPUT
    -------------------------------------------------
    output_reg_gen : if (OUTPUT_REG) generate
        signal  rdy : std_logic;
    begin

        -- set  DST_RDY when previous pipeline is ready or this
        -- stage is empty
        rdy                           <= '1' when r3_src_rdy = '0' or r3_dst_rdy = '1' else '0';
        r2_dst_rdy(BAR_SHIFT_LATENCY) <= rdy;

        process (CLK)
        begin
            if rising_edge(CLK) then
                if (RESET = '1') then
                    r3_src_rdy  <= '0';
                elsif (rdy = '1') then
                    r3_src_rdy  <= r2_src_rdy(BAR_SHIFT_LATENCY);
                end if;

                if (rdy = '1') then
                    r3_data      <= r2_data(BAR_SHIFT_LATENCY);
                    r3_metadata  <= r2_metadata(BAR_SHIFT_LATENCY);
                end if;
            end if;
        end process;
    else generate
        r3_data                        <= r2_data(BAR_SHIFT_LATENCY);
        r3_metadata                    <= r2_metadata(BAR_SHIFT_LATENCY);
        r3_src_rdy                     <= r2_src_rdy(BAR_SHIFT_LATENCY);
        r2_dst_rdy(BAR_SHIFT_LATENCY)  <= r3_dst_rdy;
    end generate;

    -------------------------------------------------
    -- SET OUTPUT
    -------------------------------------------------
    TX_DATA     <= r3_data;
    TX_METADATA <= r3_metadata;
    TX_SRC_RDY  <= r3_src_rdy;
    r3_dst_rdy  <= TX_DST_RDY;

end architecture;
