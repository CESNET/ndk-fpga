-- mi_vft.vhd: MI Virtual Function Translator
-- Copyright (C) 2017 CESNET
-- Author(s): Jan Remes
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;

library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                          ARCHITECTURE DECLARATION                         --
-- ----------------------------------------------------------------------------

architecture mi_vft_arch of MI_VFT is

   signal idcomp_map    : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal ibuf_map      : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal obuf_map      : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal rxdma_map     : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal txdma_map     : std_logic_vector(ADDR_WIDTH-1 downto 0);

    signal in_function              : std_logic_vector(7 downto 0); -- TODO

begin
    in_function <= IN_MWR(7 downto 0); -- TODO

   -- Mapping between functions and IN_FUNCTION signal values:
   --  0 -> PF0
   -- 64 -> VF0
   -- 65 -> VF1
   -- 66 -> VF2
   -- 67 -> VF3
   -- 68 -> VF4
   -- 69 -> VF5
   -- All other values are invalid at the moment
   --
   -- The mapping allows us to use bottom 5 bits of IN_FUNCTION as VF number
   -- and bit 6 (IN_FUNCTION(5)) as an FUNCTION_IS_VF flag.
   -- This will change on US+, where 256 VFs are expected

   -- ID32 mapping (plain access)
   idcomp_map  <= IN_ADDR;
   -- IBUF mapping   upper | 0x8000 |         function * 0x200        | offset
   ibuf_map    <= X"0000"  & "1000" &         IN_FUNCTION(2 downto 0) & IN_ADDR(8 downto 0);
   -- OBUF mapping   upper | 0x9000 |         function * 0x200        | offset
   obuf_map    <= X"0000"  & "1001" &         IN_FUNCTION(2 downto 0) & IN_ADDR(8 downto 0);
   -- RX DMA mapping upper | 0xC000 |         function * 0x40         | offset
   rxdma_map   <= X"0000"  & "1100" & "000" & IN_FUNCTION(2 downto 0) & IN_ADDR(5 downto 0);
   -- TX DMA mapping upper | 0xD000 |         function * 0x40         | offset
   txdma_map   <= X"0000"  & "1101" & "000" & IN_FUNCTION(2 downto 0) & IN_ADDR(5 downto 0);

   OUT_ADDR    <= IN_ADDR        when IN_FUNCTION = 0 else        -- PF0
                  IN_ADDR        when IN_FUNCTION = 1 else        -- PF1
                  X"00000078"    when IN_ADDR = X"00000040" else  -- DMA channel count
                  idcomp_map     when IN_ADDR(31 downto 8) = X"000000" else
                  ibuf_map       when IN_ADDR(31 downto 9) = (X"00008" & "000") else
                  obuf_map       when IN_ADDR(31 downto 9) = (X"00009" & "000") else
                  rxdma_map      when IN_ADDR(31 downto 6) = (X"0000C0" & "00") else
                  txdma_map      when IN_ADDR(31 downto 6) = (X"0000D0" & "00") else
                  X"FFFFFFFF";

   -- Add VFNUM to the highest byte of the Control register in the DMA controller
   OUT_DWR     <= IN_FUNCTION & IN_DWR(23 downto 0)
                                 when (IN_ADDR = X"0000C000" or IN_ADDR = X"0000D000") else
                  IN_DWR;

   OUT_BE      <= IN_BE;
   OUT_WR      <= IN_WR;
   OUT_RD      <= IN_RD;
   OUT_MWR     <= IN_MWR;

   IN_DRD      <= OUT_DRD;
   IN_DRDY     <= OUT_DRDY;
   IN_ARDY     <= OUT_ARDY;

end mi_vft_arch;
