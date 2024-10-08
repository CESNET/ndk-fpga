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
   constant reset_time     : time := 2*clkper + 0.5 ns; --Reset durati

   constant EN_DSP            : boolean := true;
   constant PACKET_LENGTH_WD  : integer := 16;
   constant NUM_BYTES_WD      : integer := 48;
   constant NUM_PACKETS_WD    : integer := 48;
   constant ADDRESS_WIDTH     : integer := 10;
   constant CNT_WIDTH         : integer := 10;

   signal CLK              : std_logic;
   signal RESET            : std_logic;

   type flt_pac_t is record
      CNT_ADDRESS       : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      PACKET_LENGTH     : std_logic_vector(PACKET_LENGTH_WD-1 downto 0);
      ADD_PACKET        : std_logic;
      SRC_RDY           : std_logic;
      DST_RDY           : std_logic;
   end record;

   type mi_t is record
      MI32_ADDR         : std_logic_vector(31 downto 0);
      MI32_WR           : std_logic;
      MI32_DWR          : std_logic_vector(31 downto 0);
      MI32_RD           : std_logic;
      MI32_DRD          : std_logic_vector(31 downto 0);
      MI32_DRDY         : std_logic;
      MI32_ARDY         : std_logic;
      MI32_BE           : std_logic_vector(3 downto 0);
   end record;

   type tr_num_t is record
      ADD_TR            : std_logic;
      ADD_RDY           : std_logic;
      RM_TR             : std_logic;
      RM_RDY            : std_logic;
   end record;

   type flt_t is record
      FILTER_ADDR       : std_logic_vector(ADDRESS_WIDTH-1 downto 0);
      FILTER_RM         : std_logic;
      FILTER_RM_ALL     : std_logic;
      FILTER_NEXT       : std_logic;
   end record;

   signal mi_i       : mi_t;
   signal tr_num_i   : tr_num_t;
   signal flt_i      : flt_t;
   signal flt_pac_i  : flt_pac_t;

   signal mi_o       : mi_t;
   signal tr_num_o   : tr_num_t;
   signal flt_o      : flt_t;
   signal flt_pac_o  : flt_pac_t;

   procedure init (
      signal mi : out mi_t;
      signal tr_num : out tr_num_t;
      signal flt_pac : out flt_pac_t;
      signal flt : out flt_t
   )is
   begin
      mi.MI32_ADDR      <= (others => '0');
      mi.MI32_WR        <= '0';
      mi.MI32_DWR       <= (others => '0');
      mi.MI32_RD        <= '0';
      mi.MI32_BE        <= (others => '0');

      tr_num.ADD_TR     <= '0';
      tr_num.ADD_RDY    <= '0';
      tr_num.RM_TR      <= '0';
      tr_num.RM_RDY     <= '0';

      flt.FILTER_ADDR   <= (others => '0');
      flt.FILTER_RM     <= '0';
      flt.FILTER_RM_ALL <= '0';

      flt_pac.CNT_ADDRESS   <= (others => '0');
      flt_pac.PACKET_LENGTH <= (others => '0');
      flt_pac.ADD_PACKET    <= '0';
      flt_pac.SRC_RDY       <= '1';
	   wait for reset_time;
      wait for clkper;
   end procedure;

   procedure tr_add (
      signal tr_num : out tr_num_t;
      num : in integer
   ) is
   begin
      tr_num.ADD_TR <= '1';
      for I in 0 to num-1 loop
         tr_num.ADD_RDY <= '1';
         wait for clkper;
         tr_num.ADD_RDY <= '0';
      end loop;
   end procedure;

   procedure tr_remove (
      signal tr_num : out tr_num_t;
      num : in integer
   ) is
   begin
      tr_num.RM_TR <= '1';
      for I in 0 to num-1 loop
         tr_num.RM_RDY <= '1';
         wait for clkper;
         tr_num.RM_RDY <= '0';
      end loop;
   end procedure;


   procedure flt_send (
      signal flt_in : out flt_t;
      signal flt_out  : in flt_t;
      addr : in integer;
      rm_all : in boolean;
      num : in integer
   )is
   begin
      for I in 0 to num-1 loop
         flt_in.FILTER_ADDR <= conv_std_logic_vector(addr, ADDRESS_WIDTH);
         if(rm_all = true) then
            flt_in.FILTER_RM_ALL <= '1';
         else
            flt_in.FILTER_RM_ALL <= '0';
         end if;
         flt_in.FILTER_RM <= '1';

         while flt_out.FILTER_NEXT = '0' loop
            wait for clkper;
         end loop;
         wait for clkper;
         flt_in.FILTER_RM <= '0';
      end loop;
   end procedure;

   procedure test_tr_num (
      signal tr_num : out tr_num_t
   )is
   begin
      tr_add(tr_num, 20);
      tr_remove(tr_num, 5);
      wait for 2*clkper;
      tr_remove(tr_num, 2);
      tr_add(tr_num, 9);
      wait for 2*clkper;
      tr_num.RM_TR   <= '1';
      tr_num.RM_RDY  <= '1';
      tr_num.ADD_TR  <= '1';
      tr_num.ADD_RDY <= '1';
      wait for clkper;
      tr_num.RM_RDY  <= '0';
      tr_num.ADD_RDY <= '0';
      tr_remove(tr_num, 22);
   end procedure;

   procedure test_wait (
      signal flt_in : out flt_t;
      signal flt_out  : in flt_t;
      signal tr_num : out tr_num_t
   ) is
   begin
      flt_send(flt_in, flt_out, 0, false, 2);
      tr_add(tr_num, 1);
      flt_send(flt_in, flt_out, 0, false, 2);
      tr_add(tr_num, 9);
      flt_send(flt_in, flt_out, 0, false, 2);
      tr_remove(tr_num, 10);
      flt_send(flt_in, flt_out, 0, false, 2);
   end procedure;

   procedure test_tr_gen (
      signal flt_in : out flt_t;
      signal flt_out  : in flt_t
   ) is
   begin
      flt_send(flt_in, flt_out, 4, false, 2);
      flt_send(flt_in, flt_out, 5, true, 1);
      wait for 5*clkper;
      flt_send(flt_in, flt_out, 6, false, 1);
   end procedure;


   procedure mi_wr_req (
      signal mi : out mi_t;
      cnt : in integer
   ) is
   begin
      mi.MI32_ADDR   <= conv_std_logic_vector(0, 32);
      mi.MI32_WR     <= '1';
      mi.MI32_DWR    <= conv_std_logic_vector(cnt, 32);
      wait for clkper;
      mi.MI32_WR <= '0';
   end procedure;

   procedure mi_rd_req (
      signal mi_in : out mi_t;
      signal mi_out : in mi_t
   ) is
   begin
      mi_in.MI32_ADDR   <= conv_std_logic_vector(4, 32);
      mi_in.MI32_RD     <= '1';
      wait for clkper;
      while mi_out.MI32_DRD(0) = '0' loop
         wait for clkper;
      end loop;
      wait for clkper;
      mi_in.MI32_ADDR   <= conv_std_logic_vector(12, 32);
      wait for clkper;
      mi_in.MI32_ADDR   <= conv_std_logic_vector(16, 32);
      wait for clkper;
      mi_in.MI32_ADDR   <= conv_std_logic_vector(20, 32);
      wait for clkper;
      mi_in.MI32_ADDR   <= conv_std_logic_vector(24, 32);
      wait for clkper;
      mi_in.MI32_RD <= '0';
   end procedure;

   procedure send_pac (
      signal flt_pac_in  : out flt_pac_t;
      signal flt_pac_out : in flt_pac_t;
      num     : in integer;
      address : in integer;
      length  : in integer
   ) is
   begin
      for I in 0 to num-1 loop
	      flt_pac_in.CNT_ADDRESS   <= conv_std_logic_vector(address, ADDRESS_WIDTH);
	      flt_pac_in.PACKET_LENGTH <= conv_std_logic_vector(length, PACKET_LENGTH_WD);
	      flt_pac_in.ADD_PACKET    <= '1';
	      flt_pac_in.SRC_RDY       <= '1';

	      while flt_pac_out.DST_RDY = '0' loop
            wait for clkper;
         end loop;
         wait for clkper;
         flt_pac_in.SRC_RDY      <= '0';
	   end loop;
   end procedure;

begin

   uut : entity work.CONTROL_STATS
   generic map (
      EN_DSP            => EN_DSP,
      PACKET_LENGTH_WD  => PACKET_LENGTH_WD,
      NUM_BYTES_WD      => NUM_BYTES_WD,
      NUM_PACKETS_WD    => NUM_PACKETS_WD,
      ADDRESS_WIDTH     => ADDRESS_WIDTH,
      CNT_WIDTH         => CNT_WIDTH
   )
   port map (
      CLK               => CLK,
      RESET             => RESET,
      MI32_ADDR         => mi_i.MI32_ADDR,
      MI32_WR           => mi_i.MI32_WR,
      MI32_DWR          => mi_i.MI32_DWR ,
      MI32_RD           => mi_i.MI32_RD,
      MI32_DRD          => mi_o.MI32_DRD ,
      MI32_DRDY         => mi_o.MI32_DRDY,
      MI32_ARDY         => mi_o.MI32_ARDY,
      MI32_BE           => mi_i.MI32_BE,
      ADD_TR            => tr_num_i.ADD_TR,
      ADD_RDY           => tr_num_i.ADD_RDY,
      RM_TR             => tr_num_i.RM_TR,
      RM_RDY            => tr_num_i.RM_RDY,
      FILTER_ADDR       => flt_i.FILTER_ADDR,
      FILTER_RM         => flt_i.FILTER_RM,
      FILTER_RM_ALL     => flt_i.FILTER_RM_ALL,
      FILTER_NEXT       => flt_o.FILTER_NEXT,
      CNT_ADDRESS       => flt_pac_i.CNT_ADDRESS,
      PACKET_LENGTH     => flt_pac_i.PACKET_LENGTH,
      ADD_PACKET        => flt_pac_i.ADD_PACKET,
      SRC_RDY           => flt_pac_i.SRC_RDY,
      DST_RDY           => flt_pac_o.DST_RDY
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
      init(mi_i, tr_num_i, flt_pac_i, flt_i);
      mi_wr_req(mi_i, 1);
      mi_rd_req(mi_i, mi_o);
      wait;
   end process input_flow;
end architecture;
