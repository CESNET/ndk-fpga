-- sqr_dop2_lat1.vhd: Squarer with 2 parts and latency of 1 clock cycles
-- Copyright (C) 2009 CESNET
-- Author(s): Ondrej Lengal <lengal@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

--library unisim;
--use unisim.vcomponents.all;

-- ==========================================================================
--                              ENTITY DECLARATION
-- ==========================================================================
entity SQR_DOP2_LAT1 is
   generic
   (
      -- widths of operands
      OPERAND_WIDTH         : integer := 34;
      -- width of result
      RESULT_WIDTH          : integer := 68
   );
   port
   (
      -- common interface
      CLK       :  in std_logic;

      -- operand
      DATA      :  in std_logic_vector(OPERAND_WIDTH-1 downto 0);

      -- result (is valid 2 clock cycles after operands are set)
      RESULT    : out std_logic_vector(RESULT_WIDTH-1 downto 0)
   );
end entity;


-- ==========================================================================
--                           ARCHITECTURE DESCRIPTION
-- ==========================================================================
architecture arch of SQR_DOP2_LAT1 is

-- ==========================================================================
--                                      TYPES
-- ==========================================================================

   -- attribute not to merge logic blocks, should prevent pushing registers
   -- into DSP block
   attribute keep      : string;

   -- attribute for the use of DSP48 for adders
   attribute use_dsp48 : string;

-- ==========================================================================
--                                    CONSTANTS
-- ==========================================================================

   -- constants for ranges
   constant IN_RNG       : integer := OPERAND_WIDTH / 2;
   constant RES_RNG      : integer := 2 * IN_RNG;
   constant RES_HALF_RNG : integer := RES_RNG / 2;

   -- assignment of bit numbers for input
   constant IN_LOWER_LSB    : integer := 0;
   constant IN_LOWER_MSB    : integer := IN_LOWER_LSB + IN_RNG - 1;
   constant IN_HIGHER_LSB   : integer := IN_LOWER_MSB + 1;
   constant IN_HIGHER_MSB   : integer := IN_HIGHER_LSB + IN_RNG - 1;

   -- assignment of bit numbers for result
   constant RES_LOWER_LSB   : integer := 0;
   constant RES_LOWER_MSB   : integer := RES_LOWER_LSB + RES_RNG - 1;
   constant RES_HIGHER_LSB  : integer := RES_LOWER_MSB + 1;
   constant RES_HIGHER_MSB  : integer := RES_HIGHER_LSB + RES_RNG - 1;
   constant RES_HILO_LSB    : integer := IN_RNG;
   constant RES_HILO_MSB    : integer := RES_HILO_LSB + RES_RNG - 1;


-- ==========================================================================
--                                     SIGNALS
-- ==========================================================================

   -- split input operands
   signal data_lo     : std_logic_vector(IN_RNG-1 downto 0);
   signal data_hi     : std_logic_vector(IN_RNG-1 downto 0);

   -- multiplication partial results
   signal mult_hihi   : std_logic_vector(RES_RNG-1 downto 0);
   signal mult_hilo   : std_logic_vector(RES_RNG-1 downto 0);
   signal mult_lolo   : std_logic_vector(RES_RNG-1 downto 0);

   -- registers for saving multipliers result
   signal reg_mult_hihi   : std_logic_vector(RES_RNG-1 downto 0);
   signal reg_mult_hilo   : std_logic_vector(RES_RNG-1 downto 0);
   signal reg_mult_lolo   : std_logic_vector(RES_RNG-1 downto 0);

   -- adder
   signal sum_lo_in0  : std_logic_vector(RES_HALF_RNG-1 downto 0);
   signal sum_lo_in1  : std_logic_vector(RES_HALF_RNG-1 downto 0);
   signal sum_lo      : std_logic_vector(RES_HALF_RNG-1 downto 0);

   signal sum_hi_cin  : std_logic;
   signal sum_hi_in0  : std_logic_vector(RES_HALF_RNG+1 downto 0);
   signal sum_hi_in1  : std_logic_vector(RES_HALF_RNG+1 downto 0);
   signal sum_hi      : std_logic_vector(RES_HALF_RNG+1 downto 0);

   signal highest     : std_logic_vector(RES_HALF_RNG-2 downto 0);

   signal sum_all     : std_logic_vector(RESULT_WIDTH-1 downto 0);

   -- implement adders in DSPs
   -- NOTE: I commented it out because XST is stupid and if you wanted to
   --       store the result into a register, it moved the register into the
   --       DSP no matter that you had a computation behind that register,
   --       therefore the critical path was lengthened
   --attribute use_dsp48 of sum_lo : signal is "yes";
   --attribute use_dsp48 of sum_hi : signal is "yes";
   --attribute use_dsp48 of highest: signal is "yes";

   -- do not merge registers that may be on inputs/outputs into DSP blocks
   attribute keep of DATA      : signal is "true";
   attribute keep of RESULT    : signal is "true";

begin

   -- --------------------------------------------------------------------------
   --                              Description
   -- --------------------------------------------------------------------------
   --
   -- The squarer splits the operands into two parts and multiplies them
   -- separately while exploiting the formula, e.g. for OPERAND_WIDTH = 24:
   --
   --   (a*2^12 + b)^2 = a^2 * 2^24 + b^2 + 2^13 * a * b
   --
   -- where:
   --    a = x(23:12)
   --    b = x(11:0)
   --


   -- --------------------------------------------------------------------------
   --                               Assertions
   -- --------------------------------------------------------------------------

   assert (OPERAND_WIDTH mod 2 = 0)
      report "Only even width of operand supported!"
      severity failure;


   -- --------------------------------------------------------------------------
   --                                 Inputs
   -- --------------------------------------------------------------------------

   data_lo <= DATA(IN_LOWER_MSB  downto  IN_LOWER_LSB);
   data_hi <= DATA(IN_HIGHER_MSB downto IN_HIGHER_LSB);


   -- --------------------------------------------------------------------------
   --                             Multiplication
   -- --------------------------------------------------------------------------

   -- partial multiplications
   mult_hihi <= data_hi * data_hi;
   mult_hilo <= data_hi * data_lo;
   mult_lolo <= data_lo * data_lo;


   -- --------------------------------------------------------------------------
   --                          Pipelining registers
   -- --------------------------------------------------------------------------

   reg_mult_hihi_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         reg_mult_hihi <= mult_hihi;
      end if;
   end process;

   reg_mult_hilo_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         reg_mult_hilo <= mult_hilo;
      end if;
   end process;

   reg_mult_lolo_p: process (CLK)
   begin
      if (rising_edge(CLK)) then
         reg_mult_lolo <= mult_lolo;
      end if;
   end process;


   -- --------------------------------------------------------------------------
   --                               Addition
   -- --------------------------------------------------------------------------

   -- addition of lower part of the result
   sum_lo_in0 <= '0' & reg_mult_hilo(RES_HALF_RNG-2 downto 0);
   sum_lo_in1 <= '0' & reg_mult_lolo(RES_RNG-1 downto RES_HALF_RNG+1);
   sum_lo     <= sum_lo_in0 + sum_lo_in1;

   -- addition of higher part of the result
   sum_hi_cin <= sum_lo(RES_HALF_RNG-1);
   sum_hi_in0 <= '0' & reg_mult_hihi(RES_HALF_RNG downto 0);
   sum_hi_in1 <= '0' & reg_mult_hilo(RES_RNG-1 downto RES_HALF_RNG-1);
   sum_hi     <= sum_hi_in0 + sum_hi_in1 + sum_hi_cin;

   -- adding to the highest part
   highest    <= reg_mult_hihi(RES_RNG-1 downto RES_HALF_RNG+1)
                 + sum_hi(RES_HALF_RNG+1);

   -- composing the whole sum into a single vector
   sum_all    <= highest
                 & sum_hi(RES_HALF_RNG   downto 0)
                 & sum_lo(RES_HALF_RNG-2 downto 0)
                 & reg_mult_lolo(RES_HALF_RNG downto 0);

   -- --------------------------------------------------------------------------
   --                                Output
   -- --------------------------------------------------------------------------

   RESULT <= sum_all;

end architecture;
