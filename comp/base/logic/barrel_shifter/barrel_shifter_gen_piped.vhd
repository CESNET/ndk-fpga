-- barrel_shifter_gen.vhd: Barrel shifter with generic data width, generic block size and optional pipelining and output register
-- Copyright (C) 2019 CESNET
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
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
    SHIFT_LEFT  : boolean := false ;

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
end BARREL_SHIFTER_GEN_PIPED;

-- ----------------------------------------------------------------------------
--                       ARCHITECTURE DECLARATION                            --
-- ----------------------------------------------------------------------------

architecture full of BARREL_SHIFTER_GEN_PIPED is

    function getMuxMetadata(metadata : std_logic_vector; index : integer) return std_logic_vector is
    begin
        if (index=0) then
            return metadata;
        else
            return (metadata'high downto 0 => '0');
        end if;
    end function;

    signal data_in_deser   : slv_array_t(BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal mux_in          : slv_array_2d_t(BLOCKS-1 downto 0)(BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal mux_in_dst_rdy  : std_logic_vector(BLOCKS-1 downto 0);
    signal mux_out         : slv_array_t(BLOCKS-1 downto 0)(BLOCK_WIDTH-1 downto 0);
    signal mux_meta_out    : slv_array_t(BLOCKS-1 downto 0)(METADATA_WIDTH-1 downto 0);
    signal mux_out_src_rdy : std_logic_vector(BLOCKS-1 downto 0);
begin

    data_in_deser <= slv_array_downto_deser(RX_DATA, BLOCKS, BLOCK_WIDTH);
    RX_DST_RDY    <= mux_in_dst_rdy(0);

    mux_leftg: if SHIFT_LEFT = true generate
        mux_leftgg: for i in 0 to BLOCKS-1 generate
            mux_leftggg: for j in 0 to BLOCKS-1 generate
                mux_in(i)(j) <= data_in_deser((i-j) mod BLOCKS);
            end generate;
        end generate;
    end generate;

    mux_rightg: if SHIFT_LEFT = false generate
        mux_rightgg: for i in 0 to BLOCKS-1 generate
            mux_rightggg: for j in 0 to BLOCKS-1 generate
                mux_in(i)(j) <= data_in_deser((j+i) mod BLOCKS);
            end generate;
        end generate;
    end generate;

    muxg: for i in 0 to BLOCKS-1 generate
        muxi: entity work.GEN_MUX_PIPED
        generic map(
            DATA_WIDTH     => BLOCK_WIDTH,
            MUX_WIDTH      => BLOCKS,
            MUX_LATENCY    => BAR_SHIFT_LATENCY,
            INPUT_REG      => INPUT_REG,
            OUTPUT_REG     => OUTPUT_REG,
            METADATA_WIDTH => METADATA_WIDTH
        )
        port map(
            CLK   => CLK,
            RESET => RESET,

            RX_DATA     => slv_array_ser(mux_in(i), BLOCKS, BLOCK_WIDTH),
            RX_SEL      => RX_SEL,
            RX_METADATA => getMuxMetadata(RX_METADATA,i), -- only propagate the real metadata through the firts multiplexer
            RX_SRC_RDY  => RX_SRC_RDY,
            RX_DST_RDY  => mux_in_dst_rdy(i),

            TX_DATA     => mux_out(i),
            TX_METADATA => mux_meta_out(i),
            TX_SRC_RDY  => mux_out_src_rdy(i),
            TX_DST_RDY  => TX_DST_RDY
        );
    end generate;

    TX_DATA     <= slv_array_ser(mux_out, BLOCKS, BLOCK_WIDTH);
    TX_METADATA <= mux_meta_out(0);
    TX_SRC_RDY  <= mux_out_src_rdy(0);

end full;
