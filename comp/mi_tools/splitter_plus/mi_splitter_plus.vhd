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
--                             ENTITY DECLARATION                            --
-- ----------------------------------------------------------------------------

-- Unlike MI_SPLITTER, components connected to MI_SPLITTER_PLUS see whole
-- global address (as it comes to MI_SPLITTER_PLUS), not it's local address.
-- If you need, you can connect MI_ADDR_SUBTRACTOR to convert global address
-- to local (subtract base of address space from the address).

entity MI_SPLITTER_PLUS is -- DEPRECATED!
   generic(
      -- Data width
      DATA_WIDTH    : integer := 32;
      -- Meta width
      META_WIDTH    : integer := 2;
      -- Number of output ports
      ITEMS         : integer := 2;
      -- Bits of address that are needed to determine output port.
      -- (see example in documentation if you don't know)
      ADDR_CMP_MASK : std_logic_vector(31 downto 0) := X"FFFFFFFF";
      -- Bases of address spaces (base of port0 is 0x00000000)
      PORT1_BASE    : std_logic_vector(31 downto 0) := X"00001000";
      PORT2_BASE    : std_logic_vector(31 downto 0) := X"00002000";
      PORT3_BASE    : std_logic_vector(31 downto 0) := X"00004000";
      PORT4_BASE    : std_logic_vector(31 downto 0) := X"00005000";
      PORT5_BASE    : std_logic_vector(31 downto 0) := X"00006000";
      PORT6_BASE    : std_logic_vector(31 downto 0) := X"00007000";
      PORT7_BASE    : std_logic_vector(31 downto 0) := X"00008000";
      -- Output pipeline
      PIPE_TYPE     : string := "SHREG";
      PIPE          : boolean := false;
      PIPE_OUTREG   : boolean := false;

      DEVICE        : string  := "7SERIES"
   );
   port(
      -- Common interface -----------------------------------------------------
      CLK         : in std_logic;
      RESET       : in std_logic;

      -- Input MI interface ---------------------------------------------------
      IN_DWR      : in  std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_MWR      : in  std_logic_vector(META_WIDTH-1 downto 0) := (others => '0');
      IN_ADDR     : in  std_logic_vector(31 downto 0);
      IN_BE       : in  std_logic_vector(DATA_WIDTH/8-1 downto 0);
      IN_RD       : in  std_logic;
      IN_WR       : in  std_logic;
      IN_ARDY     : out std_logic;
      IN_DRD      : out std_logic_vector(DATA_WIDTH-1 downto 0);
      IN_DRDY     : out std_logic;

      -- Output MI interfaces -------------------------------------------------
      OUT_DWR     : out std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_MWR     : out std_logic_vector(ITEMS*META_WIDTH-1 downto 0);
      OUT_ADDR    : out std_logic_vector(ITEMS*32-1 downto 0);
      OUT_BE      : out std_logic_vector(ITEMS*DATA_WIDTH/8-1 downto 0);
      OUT_RD      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_WR      : out std_logic_vector(ITEMS-1 downto 0);
      OUT_ARDY    : in  std_logic_vector(ITEMS-1 downto 0);
      OUT_DRD     : in  std_logic_vector(ITEMS*DATA_WIDTH-1 downto 0);
      OUT_DRDY    : in  std_logic_vector(ITEMS-1 downto 0)

   );
end entity MI_SPLITTER_PLUS;

architecture FULL of MI_SPLITTER_PLUS is

    function ADDR_BASE return slv_array_t is
        variable a0_base : slv_array_t(    8-1 downto 0)(32-1 downto 0) := (others => (others => '0'));
        variable a1_base : slv_array_t(ITEMS-1 downto 0)(32-1 downto 0) := (others => (others => '0'));
    begin

        a0_base(1) := PORT1_BASE;
        a0_base(2) := PORT2_BASE;
        a0_base(3) := PORT3_BASE;
        a0_base(4) := PORT4_BASE;
        a0_base(5) := PORT5_BASE;
        a0_base(6) := PORT6_BASE;
        a0_base(7) := PORT7_BASE;

        for i in 0 to ITEMS-1 loop
            a1_base(i) := a0_base(i);
        end loop;

        return a1_base;
    end function;

    signal out_mod_dwr  : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH-1 downto 0);
    signal out_mod_mwr  : slv_array_t(ITEMS-1 downto 0)(META_WIDTH-1 downto 0);
    signal out_mod_addr : slv_array_t(ITEMS-1 downto 0)(32-1 downto 0);
    signal out_mod_be   : slv_array_t(ITEMS-1 downto 0)(DATA_WIDTH/8-1 downto 0);

begin

    -- Use a more advanced component MI Splitter Plus Gen
    mi_splitter_plus_gen_i : entity work.MI_SPLITTER_PLUS_GEN
    generic map(
        ADDR_WIDTH  => 32                        ,
        DATA_WIDTH  => DATA_WIDTH                ,
        META_WIDTH  => META_WIDTH                ,
        PORTS       => ITEMS                     ,
        PIPE_OUT    => (ITEMS-1 downto 0 => PIPE),
        PIPE_TYPE   => PIPE_TYPE                 ,
        PIPE_OUTREG => PIPE_OUTREG               ,
        ADDR_MASK   => ADDR_CMP_MASK             ,
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

    OUT_DWR  <= slv_array_ser(out_mod_dwr );
    OUT_MWR  <= slv_array_ser(out_mod_mwr );
    OUT_ADDR <= slv_array_ser(out_mod_addr);
    OUT_BE   <= slv_array_ser(out_mod_be  );

end;
