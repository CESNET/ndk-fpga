-- mvb_item_collision_resolver.vhd:
-- Copyright (C) 2024 CESNET
-- Author(s): Daniel Kondys <kondys@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- The component MVB_ITEM_COLLISION_RESOLVER ensures that only Items with different data are valid at the output in each clock cycle.
-- When the data at the output are the same, they are invalidated (all but one).
--
-- The data are stored in a FIFO and await to be read.
-- After each read (TX_DST_RDY='1'), the logic analyzes the output data anew and recalculates the valid signal (TX_VALID).
-- This mechanism nullifies Item collisions at the cost of lowering the throughput in such cases.
--
entity MVB_ITEM_COLLISION_RESOLVER is
generic (
    ITEM_WIDTH : natural := 10;
    META_WIDTH : natural := 10;
    ITEMS      : natural := 4;
    DEVICE     : string  := "AGILEX"
);
port (
    CLK        : in  std_logic;
    RESET      : in  std_logic;

    RX_DATA    : in  slv_array_t     (ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    RX_META    : in  slv_array_t     (ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    RX_VALID   : in  std_logic_vector(ITEMS-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    TX_DATA    : out slv_array_t     (ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    TX_META    : out slv_array_t     (ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    TX_VALID   : out std_logic_vector(ITEMS-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic

);
end entity;

architecture FULL of MVB_ITEM_COLLISION_RESOLVER is

    constant FIFOXM_WIDTH : natural := META_WIDTH + ITEM_WIDTH;

    signal fifoxm_din_arr           : slv_array_t     (ITEMS-1 downto 0)(FIFOXM_WIDTH-1 downto 0);
    signal fifoxm_din               : std_logic_vector(ITEMS*            FIFOXM_WIDTH-1 downto 0);
    signal fifoxm_write             : std_logic_vector(ITEMS-1 downto 0);
    signal fifoxm_full              : std_logic;
    signal fifoxm_dout              : std_logic_vector(ITEMS*            FIFOXM_WIDTH-1 downto 0);
    signal fifoxm_read              : std_logic_vector(ITEMS-1 downto 0);
    signal fifoxm_read_inner        : std_logic_vector(ITEMS-1 downto 0);
    signal fifoxm_empty             : std_logic_vector(ITEMS-1 downto 0);
    signal fifoxm_dout_arr          : slv_array_t     (ITEMS-1 downto 0)(FIFOXM_WIDTH-1 downto 0);
    signal tx_meta_arr              : slv_array_t     (ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    signal tx_data_arr              : slv_array_t     (ITEMS-1 downto 0)(ITEM_WIDTH-1 downto 0);
    signal item_same                : std_logic_vector(ITEMS-1 downto 1);

begin

    fifoxm_din_g : for i in 0 to ITEMS-1 generate
        fifoxm_din_arr(i) <= RX_META(i) & RX_DATA(i);
    end generate;

    fifoxm_din   <= slv_array_ser(fifoxm_din_arr);
    fifoxm_write <= RX_VALID and RX_SRC_RDY;
    RX_DST_RDY   <= not fifoxm_full;

    -- Pure shakedown could be used instead of FIFOXM.
    -- Also, no shakedown should be a possibility as well.
    shakedown_i : entity work.FIFOX_MULTI
    generic map(
        DATA_WIDTH          => FIFOXM_WIDTH,
        ITEMS               => 32          ,
        WRITE_PORTS         => ITEMS       ,
        READ_PORTS          => ITEMS       ,
        RAM_TYPE            => "AUTO"      ,
        DEVICE              => DEVICE      ,
        ALMOST_FULL_OFFSET  => 0           ,
        ALMOST_EMPTY_OFFSET => 0           ,
        ALLOW_SINGLE_FIFO   => True        ,
        SAFE_READ_MODE      => False
    )
    port map(
        CLK     => CLK         ,
        RESET   => RESET       ,

        DI      => fifoxm_din  ,
        WR      => fifoxm_write,
        FULL    => fifoxm_full ,
        AFULL   => open        ,

        DO      => fifoxm_dout ,
        RD      => fifoxm_read ,
        EMPTY   => fifoxm_empty,
        AEMPTY  => open
    );

    fifoxm_read <= fifoxm_read_inner and TX_DST_RDY;

    fifoxm_dout_arr <= slv_array_deser(fifoxm_dout, ITEMS);
    fifoxm_dout_g : for i in 0 to ITEMS-1 generate
        tx_meta_arr(i) <= fifoxm_dout_arr(i)(FIFOXM_WIDTH-1 downto ITEM_WIDTH);
        tx_data_arr(i) <= fifoxm_dout_arr(i)(ITEM_WIDTH  -1 downto          0);
    end generate;

    process(all)
    begin
        item_same <= (others => '0'); -- validated by "not fifoxm_empty" below
        for i in 1 to ITEMS-1 loop
            for ii in i to ITEMS-1 loop
                if (tx_data_arr(i-1) = tx_data_arr(ii)) then
                    item_same(i) <= '1';
                end if;
            end loop;
        end loop;
    end process;

    -- Component's "inner" read: signals valid (and not same) Data at the output.
    fifoxm_read_inner(0) <= not fifoxm_empty(0);
    fifoxm_read_inner_g : for i in 1 to ITEMS-1 generate
        fifoxm_read_inner(i) <= not fifoxm_empty(i) when (or item_same(i downto 1) = '0') else '0';
    end generate;

    TX_DATA    <= tx_data_arr;
    TX_META    <= tx_meta_arr;
    TX_VALID   <= fifoxm_read_inner;
    TX_SRC_RDY <= or fifoxm_read_inner;

end architecture;
