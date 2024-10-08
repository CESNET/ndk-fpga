-- shreg.vhd: MFB shift register
-- Copyright (C) 2019 CESNET z. s. p. o.
-- Author(s): Jakub Cabal <cabal@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

entity MFB_SHREG is
    generic(
        -- Number of regions within a data word.
        MFB_REGIONS     : natural := 4;
        -- Region size (in blocks).
        MFB_REGION_SIZE : natural := 8;
        -- Block size (in items).
        MFB_BLOCK_SIZE  : natural := 8;
        -- Item width (in bits).
        MFB_ITEM_WIDTH  : natural := 8;
        -- Shift register depth in items.
        SHREG_DEPTH     : natural := 16;
        -- FPGA device name.
        DEVICE          : string := "STRATIX10"
    );
    port(
        CLK        : in  std_logic;
        RESET      : in  std_logic;

        RX_DATA    : in  std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        RX_SOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        RX_EOF_POS : in  std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        RX_SOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_EOF     : in  std_logic_vector(MFB_REGIONS-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        TX_DATA    : out std_logic_vector(MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1 downto 0);
        TX_SOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE))-1 downto 0);
        TX_EOF_POS : out std_logic_vector(MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE))-1 downto 0);
        TX_SOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_EOF     : out std_logic_vector(MFB_REGIONS-1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic
    );
end entity;

architecture FULL of MFB_SHREG is

    constant MFB_DATA_W     : natural := MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;
    constant MFB_SOF_POS_FW : natural := MFB_REGIONS*max(1,log2(MFB_REGION_SIZE));
    constant MFB_EOF_POS_FW : natural := MFB_REGIONS*max(1,log2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));
    constant SHREG_W        : natural := 2*MFB_REGIONS+MFB_EOF_POS_FW+MFB_SOF_POS_FW+MFB_DATA_W;

    signal shreg_in  : std_logic_vector(SHREG_W-1 downto 0);
    signal shreg_out : std_logic_vector(SHREG_W-1 downto 0);
    signal shreg_vld : std_logic_vector(SHREG_DEPTH-1 downto 0);

begin

    RX_DST_RDY <= TX_DST_RDY;

    shreg_in <= RX_DATA & RX_SOF_POS & RX_EOF_POS & RX_SOF & RX_EOF;

    shreg_i : entity work.SH_REG_BASE_STATIC
    generic map(
        NUM_BITS   => SHREG_DEPTH,
        DATA_WIDTH => SHREG_W,
        DEVICE     => DEVICE
    )
    port map(
        CLK        => CLK,
        DIN        => shreg_in,
        CE         => TX_DST_RDY,
        DOUT       => shreg_out
    );

    TX_DATA    <= shreg_out(SHREG_W-1 downto 2*MFB_REGIONS+MFB_EOF_POS_FW+MFB_SOF_POS_FW);
    TX_SOF_POS <= shreg_out(2*MFB_REGIONS+MFB_EOF_POS_FW+MFB_SOF_POS_FW-1 downto 2*MFB_REGIONS+MFB_EOF_POS_FW);
    TX_EOF_POS <= shreg_out(2*MFB_REGIONS+MFB_EOF_POS_FW-1 downto 2*MFB_REGIONS);
    TX_SOF     <= shreg_out(2*MFB_REGIONS-1 downto MFB_REGIONS);
    TX_EOF     <= shreg_out(MFB_REGIONS-1 downto 0);

    process (CLK)
    begin
        if rising_edge(CLK) then
            if (RESET = '1') then
                shreg_vld <= (others => '0');
            elsif (TX_DST_RDY = '1') then
                shreg_vld <= shreg_vld(SHREG_DEPTH-2 downto 0) & RX_SRC_RDY;
            end if;
        end if;
    end process;

    TX_SRC_RDY <= shreg_vld(SHREG_DEPTH-1);

end architecture;
