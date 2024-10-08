-- eth_avst_adapter.vhd: Converts Avalon Streaming (AVST) to MFB
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal   <cabal@cesnet.cz>
--            Daniel Kondys <xkondy00@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

entity ETH_AVST_ADAPTER is
    generic(
        DATA_WIDTH     : natural := 512;
        TX_REGION_SIZE : natural := DATA_WIDTH/64;
        -- Enable simple but inefficient mode
        -- Timing issues may occur when set to false
        SIMPLE_MODE_EN : boolean := false
    );
    port(
        -- CLOCK AND RESET
        CLK              : in  std_logic;
        RESET            : in  std_logic;
        -- INPUT AVST INTERFACE (Intel Ethernet IP cores)
        IN_AVST_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        IN_AVST_SOP      : in  std_logic;
        IN_AVST_EOP      : in  std_logic;
        IN_AVST_EMPTY    : in  std_logic_vector(max(1,log2(DATA_WIDTH/8))-1 downto 0);
        IN_AVST_ERROR    : in  std_logic_vector(6-1 downto 0); -- IN_AVST_ERROR(2) indicates an undersized frame
        IN_AVST_VALID    : in  std_logic;
        IN_RX_PCS_READY  : in  std_logic;
        IN_RX_BLOCK_LOCK : in  std_logic;
        IN_RX_AM_LOCK    : in  std_logic;
        -- OUTPUT MFB INTERFACE
        -- (RX MAC LITE, allowed MFB configurations: 1,N,8,8, N=DATA_WIDTH/64)
        OUT_MFB_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        OUT_MFB_SOF      : out std_logic_vector(1-1 downto 0);
        OUT_MFB_SOF_POS  : out std_logic_vector(max(1,log2(TX_REGION_SIZE))-1 downto 0);
        OUT_MFB_EOF      : out std_logic_vector(1-1 downto 0);
        OUT_MFB_EOF_POS  : out std_logic_vector(max(1,log2(TX_REGION_SIZE*8))-1 downto 0);
        OUT_MFB_ERROR    : out std_logic_vector(1-1 downto 0); -- aligned to EOF
        OUT_MFB_SRC_RDY  : out std_logic;
        OUT_LINK_UP      : out std_logic
    );
end entity;

architecture FULL of ETH_AVST_ADAPTER is

    -- ========================================================================
    --                              Constants
    -- ========================================================================
    constant DATA_BYTES    : natural := DATA_WIDTH/8;

    -- ========================================================================
    --                              Signals
    -- ========================================================================
    signal link_up                  : std_logic;
    signal in_avst_data_rotated     : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal last_valid_item          : std_logic_vector(max(1,log2(DATA_BYTES))-1 downto 0);

    signal in_avst_data_rotated_reg : std_logic_vector(DATA_WIDTH-1 downto 0);
    signal in_avst_sop_reg          : std_logic;
    signal in_avst_eop_reg          : std_logic;
    signal last_valid_item_reg      : std_logic_vector(max(1,log2(DATA_BYTES))-1 downto 0);
    signal in_avst_error_reg        : std_logic_vector(6-1 downto 0);
    signal in_avst_valid_reg        : std_logic;

begin

    -- ========================================================================
    --  Input logic
    -- ========================================================================
    link_up    <= IN_RX_PCS_READY and IN_RX_BLOCK_LOCK and IN_RX_AM_LOCK;

    -- rotate bytes
    data_rotation : for i in 0 to DATA_BYTES-1 generate
        in_avst_data_rotated((i+1)*8-1 downto i*8) <= IN_AVST_DATA((DATA_BYTES-i)*8-1 downto (DATA_BYTES-1-i)*8);
    end generate;

    -- eof_pos
    last_valid_item <= std_logic_vector((DATA_BYTES-1) - unsigned(IN_AVST_EMPTY));

    -- ========================================================================
    --  Input registers
    -- ========================================================================
    in_reg_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            in_avst_data_rotated_reg <= in_avst_data_rotated;
            in_avst_sop_reg          <= IN_AVST_SOP;
            in_avst_eop_reg          <= IN_AVST_EOP;
            last_valid_item_reg      <= last_valid_item;
            in_avst_error_reg        <= IN_AVST_ERROR;

            OUT_LINK_UP <= link_up; -- asynchronous signal - sent straight to output
        end if;
    end process;

    in_reg_vld_p : process (CLK)
    begin
        if (rising_edge(CLK)) then
            in_avst_valid_reg <= IN_AVST_VALID;
            if (RESET = '1') then
                in_avst_valid_reg <= '0';
            end if;
        end if;
    end process;

    -- ========================================================================
    --  Output logic
    -- ========================================================================
    shakedown_g: if ((DATA_WIDTH /= 512) or (SIMPLE_MODE_EN)) generate

        --  Shakedown not needed for bus width = 64
        OUT_MFB_DATA     <= in_avst_data_rotated_reg;
        OUT_MFB_SOF(0)   <= in_avst_sop_reg;
        OUT_MFB_SOF_POS  <= (others => '0');
        OUT_MFB_EOF(0)   <= in_avst_eop_reg;
        OUT_MFB_EOF_POS  <= last_valid_item_reg;
        OUT_MFB_ERROR(0) <= or in_avst_error_reg;
        OUT_MFB_SRC_RDY  <= in_avst_valid_reg;

    else generate

        eth_avst_adapter_shakedown_i : entity work.ETH_AVST_ADAPTER_SHAKEDOWN
        generic map(
            DATA_WIDTH     => DATA_WIDTH,
            TX_REGION_SIZE => TX_REGION_SIZE
        )
        port map(
            CLK   => CLK,
            RESET => RESET,

            IN_MFB_DATA       => in_avst_data_rotated_reg,
            IN_MFB_SOF        => in_avst_sop_reg,
            IN_MFB_EOF        => in_avst_eop_reg,
            IN_MFB_EOF_POS    => last_valid_item_reg,
            IN_MFB_ERROR(0)   => or in_avst_error_reg,
            IN_MFB_UNDERSIZED => in_avst_error_reg(2),
            IN_MFB_SRC_RDY    => in_avst_valid_reg,

            OUT_MFB_DATA    => OUT_MFB_DATA,
            OUT_MFB_SOF     => OUT_MFB_SOF,
            OUT_MFB_SOF_POS => OUT_MFB_SOF_POS,
            OUT_MFB_EOF     => OUT_MFB_EOF,
            OUT_MFB_EOF_POS => OUT_MFB_EOF_POS,
            OUT_MFB_ERROR   => OUT_MFB_ERROR,
            OUT_MFB_SRC_RDY => OUT_MFB_SRC_RDY
        );

    end generate;

end architecture;
