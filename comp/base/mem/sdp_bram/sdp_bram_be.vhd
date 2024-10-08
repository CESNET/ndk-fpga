-- sdp_bram_be.vhd: Simple Dual Port Block RAM Block Enable Wrapper
-- Copyright (C) 2021 CESNET z. s. p. o.
-- Author(s): Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;

-- A wrapper for SDP_BRAM to abstract Block Enable signal.
-- (Byte Enable with arbitrary width.)
--
entity SDP_BRAM_BE is
    Generic (
        -- Use Block Enable
        BLOCK_ENABLE   : boolean := False;
        -- Width of Block enabled by signal WR_BE
        -- Use multiples of 8 or 9 for highest effectivness
        BLOCK_WIDTH     : integer := 8;

        -- =========================================================================================
        -- Other SDP_BRAM generics
        --
        -- See entity of SDP_BRAM for more detail
        -- =========================================================================================
        DATA_WIDTH     : integer := 64;
        ITEMS          : integer := 512;
        COMMON_CLOCK   : boolean := True;
        OUTPUT_REG     : boolean := True;
        METADATA_WIDTH : integer := 0;
        DEVICE         : string := "ULTRASCALE"
    );
    Port (
        -- =========================================================================================
        -- SDP_BRAM ports
        --
        -- See entity of SDP_BRAM for more detail
        -- =========================================================================================
        WR_CLK      : in  std_logic;
        WR_RST      : in  std_logic;
        WR_EN       : in  std_logic;
        WR_BE       : in  std_logic_vector(DATA_WIDTH/BLOCK_WIDTH-1 downto 0);
        WR_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        WR_DATA     : in  std_logic_vector(DATA_WIDTH-1 downto 0);

        RD_CLK      : in  std_logic;
        RD_RST      : in  std_logic;
        RD_EN       : in  std_logic;
        RD_PIPE_EN  : in  std_logic;
        RD_META_IN  : in  std_logic_vector(METADATA_WIDTH-1 downto 0) := (others => '0');
        RD_ADDR     : in  std_logic_vector(log2(ITEMS)-1 downto 0);
        RD_DATA     : out std_logic_vector(DATA_WIDTH-1 downto 0);
        RD_META_OUT : out std_logic_vector(METADATA_WIDTH-1 downto 0);
        RD_DATA_VLD : out std_logic
    );
end entity;

architecture FULL of SDP_BRAM_BE is

    -- Choose most efficient Internal Block Width (8 or 9)
    function get_internal_block_width (block_width : integer) return integer is
        variable mod_8 : integer;
        variable mod_9 : integer;
    begin
        mod_8 := block_width mod 8;
        mod_9 := block_width mod 9;

        -- Count number of bits to the closet multiple of 8 and 9
        mod_8 := (8 - mod_8) mod 8;
        mod_9 := (9 - mod_9) mod 9;
        if (mod_9<mod_8) then
            return 9;
        end if;
        return 8;
    end function;

    constant INTERNAL_BLOCK_WIDTH : integer := get_internal_block_width(BLOCK_WIDTH);

    constant BLOCKS    : integer := DATA_WIDTH/BLOCK_WIDTH;
    constant SUBBLOCKS : integer := (BLOCK_WIDTH+(INTERNAL_BLOCK_WIDTH-1))/INTERNAL_BLOCK_WIDTH; -- divide and ceil

    signal internal_wr_be   : std_logic_vector(BLOCKS*SUBBLOCKS-1 downto 0);
    signal internal_wr_data : std_logic_vector(BLOCKS*SUBBLOCKS*INTERNAL_BLOCK_WIDTH-1 downto 0);
    signal internal_rd_data : std_logic_vector(BLOCKS*SUBBLOCKS*INTERNAL_BLOCK_WIDTH-1 downto 0);

begin

    assert (not BLOCK_ENABLE or (BLOCK_ENABLE and (DATA_WIDTH mod BLOCK_WIDTH = 0)))
        report "SDP_BRAM: Illegal value of DATA_WIDTH (" & integer'image(DATA_WIDTH) & ") and BLOCK_WIDTH (" & integer'image(BLOCK_WIDTH) & ") parameters. When BLOCK_ENABLE is True, DATA_WIDTH parameter must be N*BLOCK_WIDTH!"
        severity failure;

    --assert (false)
    --    report "DATA_WIDTH (" & integer'image(DATA_WIDTH) & " BLOCK_WIDTH (" & integer'image(BLOCK_WIDTH) & " INTERNAL_BLOCK_WIDTH (" & integer'image(INTERNAL_BLOCK_WIDTH) & " BLOCKS (" & integer'image(BLOCKS) & " SUBBLOCKS (" & integer'image(SUBBLOCKS)
    --    severity note;

    -- Generate WR_BE and WR_DATA for internal SDP_BRAM
    internal_wr_be_data_pr : process (WR_DATA,WR_BE)
    begin
        internal_wr_be   <= (others => '0');
        internal_wr_data <= (others => '0');
        for i in 0 to BLOCKS-1 loop
            internal_wr_be((i+1)*SUBBLOCKS-1 downto i*SUBBLOCKS) <= (others => WR_BE(i));
            internal_wr_data(i*SUBBLOCKS*INTERNAL_BLOCK_WIDTH+BLOCK_WIDTH-1 downto i*SUBBLOCKS*INTERNAL_BLOCK_WIDTH) <= WR_DATA((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH);
        end loop;
    end process;

    -- Internal SDP_BRAM
    internal_sdp_bram_i : entity work.SDP_BRAM
    generic map (
        DATA_WIDTH     => BLOCKS*SUBBLOCKS*INTERNAL_BLOCK_WIDTH,
        ITEMS          => ITEMS                                ,
        BLOCK_ENABLE   => BLOCK_ENABLE                         ,
        BLOCK_WIDTH    => INTERNAL_BLOCK_WIDTH                 ,
        COMMON_CLOCK   => COMMON_CLOCK                         ,
        OUTPUT_REG     => OUTPUT_REG                           ,
        METADATA_WIDTH => METADATA_WIDTH                       ,
        DEVICE         => DEVICE
    )
    port map (
        WR_CLK      => WR_CLK          ,
        WR_RST      => WR_RST          ,
        WR_EN       => WR_EN           ,
        WR_BE       => internal_wr_be  ,
        WR_ADDR     => WR_ADDR         ,
        WR_DATA     => internal_wr_data,

        RD_CLK      => RD_CLK          ,
        RD_RST      => RD_RST          ,
        RD_EN       => RD_EN           ,
        RD_PIPE_EN  => RD_PIPE_EN      ,
        RD_META_IN  => RD_META_IN      ,
        RD_ADDR     => RD_ADDR         ,
        RD_DATA     => internal_rd_data,
        RD_META_OUT => RD_META_OUT     ,
        RD_DATA_VLD => RD_DATA_VLD
    );

    -- Generate output from internal SDP_BRAM RD_DATA
    rd_data_pr : process (internal_rd_data)
    begin
        RD_DATA <= (others => '0');
        for i in 0 to BLOCKS-1 loop
            RD_DATA((i+1)*BLOCK_WIDTH-1 downto i*BLOCK_WIDTH) <= internal_rd_data(i*INTERNAL_BLOCK_WIDTH*SUBBLOCKS+BLOCK_WIDTH-1 downto i*INTERNAL_BLOCK_WIDTH*SUBBLOCKS);
        end loop;
    end process;

end architecture;
