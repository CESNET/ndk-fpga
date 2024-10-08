-- Copyright (C) 2018 CESNET
-- Author(s): Mario kuka <kuka@cesnet.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.math_pack.all;
use work.mi32_pkg.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity testbench is
end entity testbench;

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------

architecture behavioral of testbench is
   -- Synchronization
   constant CLK_PER       : time := 1.0 ns;
   constant RESET_TIME    : time := 5.2 ns;

   signal clk : std_logic;
   signal reset : std_logic;
   signal mi32 : mi32_t;

   constant SOP_POS_WIDTH   : integer := 3;
   constant DATA_WIDTH      : integer := 512;

   signal RX_DATA     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal RX_SOP_POS  : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal RX_EOP_POS  : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal RX_SOP      : std_logic;
   signal RX_EOP      : std_logic;
   signal RX_SRC_RDY  : std_logic;
   signal RX_DST_RDY  : std_logic;
   signal TX_DATA     : std_logic_vector(DATA_WIDTH-1 downto 0);
   signal TX_SOP_POS  : std_logic_vector(SOP_POS_WIDTH-1 downto 0);
   signal TX_EOP_POS  : std_logic_vector(log2(DATA_WIDTH/8)-1 downto 0);
   signal TX_SOP      : std_logic;
   signal TX_EOP      : std_logic;
   signal TX_SRC_RDY  : std_logic;
   signal TX_DST_RDY  : std_logic;
   signal IFC         : std_logic_vector(7 downto 0);
   signal IFC_SRC_RDY : std_logic;
   signal IFC_DST_RDY : std_logic;


   subtype hdr_size_range  is natural range 23+64 downto 16+64;
   subtype ifc_range       is natural range 39+64 downto 32+64;

begin

   -- -------------------------------------------------------------------------
   --                        clk and reset generators
   -- -------------------------------------------------------------------------

   -- generating dcpro_clk
   clk_gen: process
   begin
      clk <= '1';
      wait for CLK_PER / 2;
      clk <= '0';
      wait for CLK_PER / 2;
   end process clk_gen;

   -- generating dcpro_reset
   reset_gen: process
   begin
      reset <= '1';
      wait for RESET_TIME;
      reset <= '0';
      wait;
   end process reset_gen;

   -- -------------------------------------------------------------------------
   --                              UUT
   -- -------------------------------------------------------------------------

   uut: entity work.TX_DMA_EXTRACTOR
   generic map (
      SOP_POS_WIDTH => SOP_POS_WIDTH,
      DATA_WIDTH    => DATA_WIDTH
   )
   port map (
      RESET         => reset,
      CLK           => clk,
      RX_DATA       => RX_DATA,
      RX_SOP_POS    => RX_SOP_POS,
      RX_EOP_POS    => RX_EOP_POS,
      RX_SOP        => RX_SOP,
      RX_EOP        => RX_EOP,
      RX_SRC_RDY    => RX_SRC_RDY,
      RX_DST_RDY    => RX_DST_RDY,
      TX_DATA       => TX_DATA,
      TX_SOP_POS    => TX_SOP_POS,
      TX_EOP_POS    => TX_EOP_POS,
      TX_SOP        => TX_SOP,
      TX_EOP        => TX_EOP,
      TX_SRC_RDY    => TX_SRC_RDY,
      TX_DST_RDY    => TX_DST_RDY,
      IFC           => IFC,
      IFC_SRC_RDY   => IFC_SRC_RDY,
      IFC_DST_RDY   => IFC_DST_RDY
   );

   -- -------------------------------------------------------------------------
   --                          Testbench process
   -- -------------------------------------------------------------------------

   -- Simulation core
   tb: process
   begin
      RX_DATA     <= (others => '0');
      RX_SOP_POS  <= (others => '0');
      RX_EOP_POS  <= (others => '0');
      RX_SOP      <= '0';
      RX_EOP      <= '0';
      RX_SRC_RDY  <= '0';
      TX_DST_RDY  <= '1';
      IFC_DST_RDY <= '1';
      wait for reset_time;
      -- test som increment
      RX_SOP <= '1';
      RX_EOP <= '1';
      RX_SRC_RDY <= '1';
      RX_EOP_POS <= (others => '1');
      wait for clk_per;
      RX_SOP <= '0';
      RX_EOP <= '0';
      RX_SRC_RDY <= '0';
      wait for clk_per * 5;

      -- test accuracy of IFC output
      RX_DATA(ifc_range) <= std_logic_vector(to_unsigned(10, 8));
      RX_DATA(hdr_size_range) <= std_logic_vector(to_unsigned(1, 8));
      RX_SOP <= '1';
      RX_SOP_POS <= std_logic_vector(to_unsigned(1, RX_SOP_POS'length));
      RX_EOP <= '1';
      RX_SRC_RDY <= '1';
      RX_EOP_POS <= (others => '1');
      wait for clk_per;
      RX_DATA(hdr_size_range) <= std_logic_vector(to_unsigned(0, 8));
      RX_SOP <= '1';
      RX_SOP_POS <= std_logic_vector(to_unsigned(1, RX_SOP_POS'length));
      RX_EOP <= '1';
      RX_SRC_RDY <= '1';
      RX_EOP_POS <= (others => '1');
      wait for clk_per;
      RX_SOP <= '0';
      RX_EOP <= '0';
      RX_SRC_RDY <= '0';
      wait for clk_per * 5;

      -- test all flu sop pos positions
      for I in 0 to 7 loop
        RX_SOP <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(I, RX_SOP_POS'length));
        RX_EOP <= '0';
        RX_SRC_RDY <= '1';
        wait for clk_per;
        RX_SOP <= '0';
        RX_EOP <= '1';
        RX_SRC_RDY <= '1';
        RX_EOP_POS <= (others => '1');
        wait for clk_per;
      end loop;
      RX_SOP <= '0';
      RX_EOP <= '0';
      RX_SRC_RDY <= '0';
      wait for clk_per * 5;

      -- test output fifo overflow
      IFC_DST_RDY <= '0';
      for I in 0 to 63 loop
        RX_SOP <= '1';
        RX_SOP_POS <= std_logic_vector(to_unsigned(0, RX_SOP_POS'length));
        RX_EOP <= '1';
        RX_EOP_POS <= (others => '1');
        RX_SRC_RDY <= '1';
        wait for clk_per;
      end loop;
      RX_SOP <= '0';
      RX_EOP <= '0';
      RX_SRC_RDY <= '0';
      wait for clk_per * 5;

      IFC_DST_RDY <= '1';
      RX_SOP <= '0';
      RX_EOP <= '0';
      RX_SRC_RDY <= '0';
      wait for clk_per;
      wait;
   end process;

end architecture behavioral;
