-- item_reconfigurator.vhd: Implementation of MFB item_reconfigurator component
-- Copyright (C) 2020 CESNET
-- Author: Jan Kubalek <kubalek@cesnet.cz>

-- SPDX-License-Identifier: BSD-3-Clause
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                            Entity declaration
-- ----------------------------------------------------------------------------

entity MFB_ITEM_RECONFIGURATOR is
generic(
    -- =============================
    -- MFB Configuration
    -- =============================

    REGIONS        : integer := 2;
    REGION_SIZE    : integer := 1;
    RX_BLOCK_SIZE  : integer := 8;
    TX_BLOCK_SIZE  : integer := 8;
    RX_ITEM_WIDTH  : integer := 32;
    META_WIDTH     : integer := 0;

    -- =============================
    -- Others
    -- =============================

    -- Target device
    DEVICE         : string := "ULTRASCALE";

    -- Derived parameters
    -- DO NOT CHANGE!
    TX_ITEM_WIDTH  : integer := RX_ITEM_WIDTH*RX_BLOCK_SIZE/TX_BLOCK_SIZE
);
port(
    CLK   : in std_logic;
    RESET : in std_logic;

    -- =============================
    -- MFB input interface
    -- =============================

    RX_DATA    : in  std_logic_vector(REGIONS*REGION_SIZE*RX_BLOCK_SIZE*RX_ITEM_WIDTH-1 downto 0);
    RX_META    : in  std_logic_vector(REGIONS*META_WIDTH-1 downto 0) := (others => '0');
    RX_SOF     : in  std_logic_vector(REGIONS-1 downto 0);
    RX_EOF     : in  std_logic_vector(REGIONS-1 downto 0);
    RX_SOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    RX_EOF_POS : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*RX_BLOCK_SIZE))-1 downto 0);
    RX_SRC_RDY : in  std_logic;
    RX_DST_RDY : out std_logic;

    -- =============================
    -- MFB output interface
    -- =============================

    TX_DATA    : out std_logic_vector(REGIONS*REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH-1 downto 0);
    TX_META    : out std_logic_vector(REGIONS*META_WIDTH-1 downto 0);
    TX_SOF     : out std_logic_vector(REGIONS-1 downto 0);
    TX_EOF     : out std_logic_vector(REGIONS-1 downto 0);
    TX_SOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
    TX_EOF_POS : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*TX_BLOCK_SIZE))-1 downto 0);
    TX_SRC_RDY : out std_logic;
    TX_DST_RDY : in  std_logic
);
end entity;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture FULL of MFB_ITEM_RECONFIGURATOR is

    constant RX_EOF_POS_W      : natural := max(1,log2(REGION_SIZE*RX_BLOCK_SIZE));
    constant RX_EOF_POS_TRUE_W : natural := log2(REGION_SIZE*RX_BLOCK_SIZE);
    constant TX_EOF_POS_W      : natural := max(1,log2(REGION_SIZE*TX_BLOCK_SIZE));

    -- ------------------------------------------------------------------------
    -- All cases covered
    -- ------------------------------------------------------------------------

    signal RX_EOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(RX_EOF_POS_W-1 downto 0);
    signal TX_EOF_POS_arr : slv_array_t(REGIONS-1 downto 0)(TX_EOF_POS_W-1 downto 0);

    -- ------------------------------------------------------------------------

begin

    -- ------------------------------------------------------------------------
    -- Asserts over generics
    -- ------------------------------------------------------------------------

    assert (2**log2(REGIONS) = REGIONS and REGIONS > 0)
        report "MFB_ITEM_RECONFIGURATOR: REGIONS must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(REGION_SIZE) = REGION_SIZE and REGION_SIZE > 0)
        report "MFB_ITEM_RECONFIGURATOR: REGION_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_BLOCK_SIZE) = RX_BLOCK_SIZE and RX_BLOCK_SIZE > 0)
        report "MFB_ITEM_RECONFIGURATOR: RX_BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(TX_BLOCK_SIZE) = TX_BLOCK_SIZE and TX_BLOCK_SIZE > 0)
        report "MFB_ITEM_RECONFIGURATOR: TX_BLOCK_SIZE must be power of 2 and higher than 0."
        severity failure;
    assert (2**log2(RX_ITEM_WIDTH) = RX_ITEM_WIDTH and RX_ITEM_WIDTH > 0)
        report "MFB_ITEM_RECONFIGURATOR: RX_ITEM_WIDTH must be power of 2 and higher than 0."
        severity failure;

    -- ------------------------------------------------------------------------

    -- ------------------------------------------------------------------------
    -- All cases covered
    -- ------------------------------------------------------------------------

    TX_DATA    <= RX_DATA;
    TX_META    <= RX_META;
    TX_SOF     <= RX_SOF;
    TX_EOF     <= RX_EOF;
    TX_SOF_POS <= RX_SOF_POS;
    TX_SRC_RDY <= RX_SRC_RDY;
    RX_DST_RDY <= TX_DST_RDY;

    -- Simply add or remove bits at the end of each EOF_POS
    RX_EOF_POS_arr <= slv_array_deser(RX_EOF_POS,REGIONS);
    xof_resize_pr : process (RX_EOF_POS_arr)
    begin
        for i in 0 to REGIONS-1 loop
            TX_EOF_POS_arr(i) <= std_logic_vector(resize_right(resize_left(unsigned(RX_EOF_POS_arr(i)),RX_EOF_POS_TRUE_W),TX_EOF_POS_W));
            -- When enlarging, fill with '1's NOT '0's!
            TX_EOF_POS_arr(i)(TX_EOF_POS_W-RX_EOF_POS_TRUE_W-1 downto 0) <= (others => '1');
        end loop;
    end process;
    TX_EOF_POS <= slv_array_ser(TX_EOF_POS_arr);

    -- ------------------------------------------------------------------------

end architecture;
