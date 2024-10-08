-- # Copyright (C) 2016 CESNET
-- # Author: Mario Kuka <xkukam00@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.std_logic_arith.all;
use work.math_pack.all;

entity testbench is

end testbench;

architecture behavioral of testbench is

   constant clkper         : time := 10 ns; --Clock period
   constant reset_time     : time := 2*clkper + 0.2 ns; --Reset durati

   constant EN_DSP            : boolean := true;
   constant NUM_BYTES_WD      : integer := 48;
   constant NUM_PACKETS_WD    : integer := 48;
   constant PACKET_LENGTH_WD  : integer := 16;
   constant REG_OUT           : integer := 0;
   constant ADDRESS_WIDTH     : integer := 10;

   type ifc_t is record
      RM_ADDRESS       : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      RM_RD_ENABLE     : std_logic;
      RM_REQ           : std_logic;
      CNT_ADDRESS      : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      PACKET_LENGTH    : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET       : std_logic;
      SRC_RDY          : std_logic;
      RD_NEXT          : std_logic;
   end record;

   signal CLK              : std_logic;
   signal RESET            : std_logic;

   signal ifc              : ifc_t;
   signal DST_RDY          : std_logic;
   signal RD_NUM_BYTES     : std_logic_vector(NUM_BYTES_WD-1 downto 0);
   signal RD_NUM_PACKETS   : std_logic_vector(NUM_PACKETS_WD-1 downto 0);
   signal RD_VLD           : std_logic;

   procedure init (signal ifc : out ifc_t) is
   begin
      ifc.RM_ADDRESS    <= (others => '0');
      ifc.RM_REQ        <= '0';
	   ifc.CNT_ADDRESS   <= (others => '0');
	   ifc.PACKET_LENGTH <= (others => '0');
	   ifc.ADD_PACKET    <= '0';
	   ifc.SRC_RDY       <= '0';
	   ifc.RD_NEXT       <= '1';
	   wait for reset_time;
      wait for clkper;
   end procedure;

   procedure send_rm (
      read    : in boolean;
      address : in integer;
      signal ifc : out ifc_t
      ) is
   begin
      ifc.RM_ADDRESS    <= conv_std_logic_vector(address, ADDRESS_WIDTH);
      ifc.RM_REQ        <= '1';
      if(read = false) then
         ifc.RM_RD_ENABLE  <= '0';
      else
         ifc.RM_RD_ENABLE  <= '1';
      end if;
	   ifc.SRC_RDY       <= '1';
      wait for clkper;
      ifc.RM_REQ        <= '0';
	   ifc.SRC_RDY       <= '0';
   end procedure;

   procedure send_pac (
      num     : in integer;
      address : in integer;
      length  : in integer;
      signal ifc : out ifc_t
      ) is
   begin
      for I in 0 to num-1 loop
	      ifc.CNT_ADDRESS   <= conv_std_logic_vector(address, ADDRESS_WIDTH);
	      ifc.PACKET_LENGTH <= conv_std_logic_vector(length, PACKET_LENGTH_WD);
	      ifc.ADD_PACKET    <= '1';
	      ifc.SRC_RDY       <= '1';
         wait for clkper;
	      ifc.SRC_RDY       <= '0';
	   end loop;
   end procedure;

   procedure combine_test (
      base_address : in integer;
      signal ifc : out ifc_t
      ) is
      type int_array is array(0 to 5-1) of integer;
      variable num : integer := 10;
      variable addrs : int_array;
   begin
      for I7 in 0 to num-1 loop
         send_rm(true, base_address + I7, ifc);
      end loop;

      for I1 in 0 to num-1 loop
         addrs(0) := I1;
         for I2 in 0 to num-1 loop
            addrs(1) := I2;
            for I3 in 0 to num-1 loop
               addrs(2) := I3;
               for I4 in 0 to num-1 loop
                  addrs(3) := I4;
                  for I5 in 0 to num-1 loop
                     addrs(4) := I5;

                     for I6 in 0 to 5-1 loop
                        send_pac(1, base_address + addrs(I6), addrs(I6)+1, ifc);
                     end loop;

	               end loop;
	            end loop;
	         end loop;
	      end loop;
      end loop;

      for I8 in 0 to num-1 loop
         send_rm(true, base_address + I8, ifc);
      end loop;

      for I8 in 0 to num-1 loop
         send_rm(true, base_address + I8, ifc);
      end loop;
   end procedure;

begin

   -- packet editor
   uut : entity work.PAC_STATS
   generic map (
      EN_DSP            => EN_DSP,
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      ADDRESS_WIDTH     => ADDRESS_WIDTH
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,
      RM_ADDRESS        => ifc.RM_ADDRESS,
      RM_RD_ENABLE      => ifc.RM_RD_ENABLE,
      RM_REQ            => ifc.RM_REQ,
      CNT_ADDRESS       => ifc.CNT_ADDRESS,
      PACKET_LENGTH     => ifc.PACKET_LENGTH,
      ADD_PACKET        => ifc.ADD_PACKET,
      SRC_RDY           => ifc.SRC_RDY,
      DST_RDY           => DST_RDY,
      RD_NUM_BYTES      => RD_NUM_BYTES,
      RD_NUM_PACKETS    => RD_NUM_PACKETS,
      RD_VLD            => RD_VLD,
      RD_NEXT           => ifc.RD_NEXT
   );

   --Generate clock
   clk_gen_p : process
   begin
      CLK <= '1';
      wait for clkper/2;
      CLK <= '0';
      wait for clkper/2;
   end process clk_gen_p;

   --Generate reset
   reset_gen : process
   begin
      RESET <= '1';
      wait for reset_time;
      RESET <= '0';
   wait;
   end process;

   -- Simulating input flow
   input_flow : process
   begin
      init(ifc);
      combine_test(400, ifc);
      wait;
   end process input_flow;
end architecture;
