-- mi_splitter.vhd: MI Splitter
-- Copyright (C) 2008 CESNET
-- Author(s): Vaclav Bartos <xbarto11@stud.fit.vutbr.cz>
--            Jan Kubalek <kubalek@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                                Description
-- ----------------------------------------------------------------------------
-- !!!     THIS UNIT HAS BEEN DEPRECATED    !!!
-- !!! USE THE MI_SPLITTER_PLUS_GEN INSTEAD !!!
--
-- (This component has been turned into a wrapper over
--  the MI_SPLITTER_PLUS_GEN for backward compatibility reasons.)

-- ----------------------------------------------------------------------------
--                                 Entity
-- ----------------------------------------------------------------------------

entity MI_SPLITTER is -- DEPRECATED!
   generic(
      ITEMS             : integer := 4;     -- number of output MI interfaces
      ADDR_WIDTH        : integer := 30;    -- address width (1-32)
      DATA_WIDTH        : integer := 32;    -- data width (8-128)
      META_WIDTH        : integer := 2;     -- meta width
      PIPE              : boolean := false; -- insert pipeline
      -- YOU CAN SELECT TYPE OF PIPE IMPLEMENTATION:
      --    "SHREG" - pipe implemented as shift register
      --    "REG"   - two-stage pipe created from two registers + 1 MUX, better
      --              on wide buses and on Intel/Altera devices
      PIPE_TYPE         : string := "SHREG";
      PIPE_OUTREG       : boolean := false; -- Only for PIPE_TYPE = "SHREG"!
      -- This generic enables the optimization of the data read side. The initial
      -- implementation infers the long combination path through LUTs.
      -- The optimized version is using the muxltiplexer which allows better
      -- implementation in the case of many outputs.
      -- However, this optimization is disabled by default (i.e., default
      -- behavior is being used).
      --
      -- Warning: The optimization consumes more resources but it allows better
      -- timing!
      DRD_OPTIMIZATION  : boolean := false;
      -- Target device
      DEVICE            : string := "7SERIES"
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
      IN_ADDR     : in  std_logic_vector((ADDR_WIDTH+log2(ITEMS))-1 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;

      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_MWR     : out std_logic_vector(ITEMS*META_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*ADDR_WIDTH-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)

   );
end entity MI_SPLITTER;

architecture mi_splitter_arch of MI_SPLITTER is

    function ADDR_BASE return slv_array_t is
        variable a_base : slv_array_t(ITEMS-1 downto 0)((ADDR_WIDTH+log2(ITEMS))-1 downto 0) := (others => (others => '0'));
    begin
        for i in 0 to ITEMS-1 loop
            a_base(i) := std_logic_vector(to_unsigned(i*2**ADDR_WIDTH,ADDR_WIDTH+log2(ITEMS)));
        end loop;

        return a_base;
    end function;

    function ADDR_MASK return std_logic_vector is
        variable a_mask : std_logic_vector(ADDR_WIDTH+log2(ITEMS)-1 downto 0) := (ADDR_WIDTH+log2(ITEMS)-1 downto ADDR_WIDTH => '1', others => '0');
    begin
        return a_mask;
    end function;

    signal out_mod_dwr  : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal out_mod_mwr  : slv_array_t(ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    signal out_mod_addr : slv_array_t(ITEMS-1 downto 0)(ADDR_WIDTH+log2(ITEMS)-1 downto 0);
    signal out_mod_be   : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH/8-1 downto 0);

    signal out_mod_mod_addr : slv_array_t(ITEMS-1 downto 0)(ADDR_WIDTH-1 downto 0);

begin

    -- Use a more advanced component MI Splitter Plus Gen
    mi_splitter_plus_gen_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH  => ADDR_WIDTH+log2(ITEMS)    ,
        DATA_WIDTH  => DATA_WIDTH                ,
        META_WIDTH  => META_WIDTH                ,
        PORTS       => ITEMS                     ,
        PIPE_OUT    => (ITEMS-1 downto 0 => PIPE),
        PIPE_TYPE   => PIPE_TYPE                 ,
        PIPE_OUTREG => PIPE_OUTREG               ,
        ADDR_MASK   => ADDR_MASK                 ,
        ADDR_BASES  => ITEMS                     ,
        ADDR_BASE   => ADDR_BASE                 ,
        DEVICE      => DEVICE
    )
    port map(
        CLK     => CLK  ,
        RESET   => RESET,

        RX_DWR  => IN_DWR ,
        RX_MWR  => IN_MWR ,
        RX_ADDR => IN_ADDR,
        RX_BE   => IN_BE  ,
        RX_RD   => IN_RD  ,
        RX_WR   => IN_WR  ,
        RX_ARDY => IN_ARDY,
        RX_DRD  => IN_DRD ,
        RX_DRDY => IN_DRDY,

        TX_DWR  => out_mod_dwr ,
        TX_MWR  => out_mod_mwr ,
        TX_ADDR => out_mod_addr,
        TX_BE   => out_mod_be  ,
        TX_RD   => OUT_RD      ,
        TX_WR   => OUT_WR      ,
        TX_ARDY => OUT_ARDY    ,
        TX_DRD  => slv_array_deser(OUT_DRD,ITEMS),
        TX_DRDY => OUT_DRDY
    );

    out_addr_gen : for i in 0 to ITEMS-1 generate
        out_mod_mod_addr(i) <= out_mod_addr(i)(ADDR_WIDTH-1 downto 0);
    end generate;

    OUT_DWR  <= slv_array_ser(out_mod_dwr     );
    OUT_MWR  <= slv_array_ser(out_mod_mwr     );
    OUT_ADDR <= slv_array_ser(out_mod_mod_addr);
    OUT_BE   <= slv_array_ser(out_mod_be      );

end;
