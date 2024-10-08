-- mfb_merger_gen.vhd: MFB+MVB bus merger with generic number of inputs
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
-- SPDX-License-Identifier: BSD-3-Clause
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

library work;
use work.math_pack.all;
use work.type_pack.all;

entity DUT_WRAPPER is
    generic(
        MERGER_INPUTS   : integer := 2;  -- number of merger inputs
        MVB_ITEMS       : integer := 2;  -- number of headers
        MVB_ITEM_WIDTH  : integer := 32; -- width of header
        MFB_REGIONS     : integer := 2;  -- number of regions in word
        MFB_REG_SIZE    : integer := 1;  -- number of blocks in region
        MFB_BLOCK_SIZE  : integer := 8;  -- number of items in block
        MFB_ITEM_WIDTH  : integer := 32; -- width  of one item (in bits)
        MFB_META_WIDTH  : integer := 1;  -- width of MFB metadata
        INPUT_FIFO_SIZE : integer := 8;
        -- THIS IS THE ONLY CHANGE FROM THE ORIGINAL ENTITY
        -- SYSTEMVERILOG DOES NOT SUPPORT 'DOWNTO' GENERICS
        -- Fixed in ModelSim-SE 2020.4
        RX_PAYLOAD_EN   : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);
        IN_PIPE_EN      : boolean := false;
        OUT_PIPE_EN     : boolean := true;
        DEVICE          : string  := "ULTRASCALE"
    );
    port(
        CLK            : in  std_logic;
        RESET          : in  std_logic;

        RX_MVB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        RX_MVB_PAYLOAD : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_VLD     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MVB_ITEMS-1 downto 0);
        RX_MVB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MVB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        RX_MFB_DATA    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_MFB_META    : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*MFB_META_WIDTH-1 downto 0) := (others => (others => '0'));
        RX_MFB_SOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_EOF     : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS-1 downto 0);
        RX_MFB_SOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        RX_MFB_EOF_POS : in  slv_array_t     (MERGER_INPUTS-1 downto 0)(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_MFB_SRC_RDY : in  std_logic_vector(MERGER_INPUTS-1 downto 0);
        RX_MFB_DST_RDY : out std_logic_vector(MERGER_INPUTS-1 downto 0);

        TX_MVB_DATA    : out std_logic_vector(MVB_ITEMS*MVB_ITEM_WIDTH-1 downto 0);
        TX_MVB_PAYLOAD : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_VLD     : out std_logic_vector(MVB_ITEMS-1 downto 0);
        TX_MVB_SRC_RDY : out std_logic;
        TX_MVB_DST_RDY : in  std_logic;

        TX_MFB_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_MFB_META    : out std_logic_vector(MFB_REGIONS*MFB_META_WIDTH-1 downto 0);
        TX_MFB_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_MFB_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE))-1 downto 0);
        TX_MFB_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REG_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_MFB_SRC_RDY : out std_logic;
        TX_MFB_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of DUT_WRAPPER is

    -- Fixed in ModelSim-SE 2020.4
    --function get_downto_en return b_array_t is
    --    variable ret : b_array_t(MERGER_INPUTS-1 downto 0) := (others => true);
    --begin
    --    for i in 0 to MERGER_INPUTS-1 loop
    --        ret(i) := RX_PAYLOAD_EN(i);
    --    end loop;
    --    return ret;
    --end function;
--
    --constant RX_PAYLOAD_EN_DOWNTO : b_array_t(MERGER_INPUTS-1 downto 0) := get_downto_en;

begin

    dut_i : entity work.MFB_MERGER_GEN
    generic map (
        MERGER_INPUTS   => MERGER_INPUTS  ,
        MVB_ITEMS       => MVB_ITEMS      ,
        MVB_ITEM_WIDTH  => MVB_ITEM_WIDTH ,
        MFB_REGIONS     => MFB_REGIONS    ,
        MFB_REG_SIZE    => MFB_REG_SIZE   ,
        MFB_BLOCK_SIZE  => MFB_BLOCK_SIZE ,
        MFB_ITEM_WIDTH  => MFB_ITEM_WIDTH ,
        MFB_META_WIDTH  => MFB_META_WIDTH ,
        INPUT_FIFO_SIZE => INPUT_FIFO_SIZE,
        RX_PAYLOAD_EN   => RX_PAYLOAD_EN,
        IN_PIPE_EN      => IN_PIPE_EN     ,
        OUT_PIPE_EN     => OUT_PIPE_EN    ,
        DEVICE          => DEVICE
    )
    port map (
        CLK            => CLK            ,
        RESET          => RESET          ,

        RX_MVB_DATA    => RX_MVB_DATA    ,
        RX_MVB_PAYLOAD => RX_MVB_PAYLOAD ,
        RX_MVB_VLD     => RX_MVB_VLD     ,
        RX_MVB_SRC_RDY => RX_MVB_SRC_RDY ,
        RX_MVB_DST_RDY => RX_MVB_DST_RDY ,

        RX_MFB_DATA    => RX_MFB_DATA    ,
        RX_MFB_META    => RX_MFB_META    ,
        RX_MFB_SOF     => RX_MFB_SOF     ,
        RX_MFB_EOF     => RX_MFB_EOF     ,
        RX_MFB_SOF_POS => RX_MFB_SOF_POS ,
        RX_MFB_EOF_POS => RX_MFB_EOF_POS ,
        RX_MFB_SRC_RDY => RX_MFB_SRC_RDY ,
        RX_MFB_DST_RDY => RX_MFB_DST_RDY ,

        TX_MVB_DATA    => TX_MVB_DATA    ,
        TX_MVB_PAYLOAD => TX_MVB_PAYLOAD ,
        TX_MVB_VLD     => TX_MVB_VLD     ,
        TX_MVB_SRC_RDY => TX_MVB_SRC_RDY ,
        TX_MVB_DST_RDY => TX_MVB_DST_RDY ,

        TX_MFB_DATA    => TX_MFB_DATA    ,
        TX_MFB_META    => TX_MFB_META    ,
        TX_MFB_SOF     => TX_MFB_SOF     ,
        TX_MFB_EOF     => TX_MFB_EOF     ,
        TX_MFB_SOF_POS => TX_MFB_SOF_POS ,
        TX_MFB_EOF_POS => TX_MFB_EOF_POS ,
        TX_MFB_SRC_RDY => TX_MFB_SRC_RDY ,
        TX_MFB_DST_RDY => TX_MFB_DST_RDY
    );

end architecture;
