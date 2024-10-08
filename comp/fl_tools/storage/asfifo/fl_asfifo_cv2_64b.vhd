-- fl_asfifo_cv2_64b.vhd : Async FL_FIFO composed of one virtex5 built-in FIFO
-- Copyright (C) 2009 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                              Entity declaration
-- ----------------------------------------------------------------------------
entity FL_ASFIFO_CV2_64B is
   port(
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_RESET       : in  std_logic;

      RX_DATA        : in  std_logic_vector(63 downto 0);
      RX_REM         : in  std_logic_vector(2 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      TX_DATA        : out std_logic_vector(63 downto 0);
      TX_REM         : out std_logic_vector(2 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end FL_ASFIFO_CV2_64B;
-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_asfifo_cv2_64b is

signal par_in     : std_logic_vector(7 downto 0);
signal par_out    : std_logic_vector(7 downto 0);

signal reset_both : std_logic;

signal sig_empty  : std_logic;
signal sig_full   : std_logic;
signal sig_rden   : std_logic;
signal sig_wren   : std_logic;

begin

   reset_both <= RX_RESET or TX_RESET;

   par_in  <= '0' & RX_SOP_N & RX_EOP_N & RX_SOF_N & RX_EOF_N & RX_REM;
   RX_DST_RDY_N <= sig_full;
   sig_wren <= not RX_SRC_RDY_N;

   FIFO36_72_inst : FIFO36_72
   generic map (
      ALMOST_FULL_OFFSET => X"0080",  -- Sets almost full threshold
      ALMOST_EMPTY_OFFSET => X"0080", -- Sets the almost empty threshold
      DO_REG => 1,                    -- Enable output register (0 or 1)
                                      -- Must be 1 if EN_SYN = FALSE
      EN_ECC_READ => FALSE,           -- Enable ECC decoder, TRUE or FALSE
      EN_ECC_WRITE => FALSE,          -- Enable ECC encoder, TRUE or FALSE
      EN_SYN => FALSE,                -- Specifies FIFO as Asynchronous (FALSE)
                                      -- or Synchronous (TRUE)
      FIRST_WORD_FALL_THROUGH => TRUE,-- Sets the FIFO FWFT to TRUE or FALSE
      SIM_MODE => "SAFE") -- Simulation: "SAFE" vs "FAST", see "Synthesis and Simulation
                          -- Design Guide" for details
   port map (
      ALMOSTEMPTY => open,          -- 1-bit almost empty output flag
      ALMOSTFULL => open,           -- 1-bit almost full output flag
      DBITERR => open,              -- 1-bit double bit error status output
      DO => TX_DATA,                -- 64-bit data output
      DOP => par_out,               -- 4-bit parity data output
      ECCPARITY => open,            -- 8-bit generated error correction parity
      EMPTY => sig_empty,           -- 1-bit empty output flag
      FULL => sig_full,             -- 1-bit full output flag
      RDCOUNT => open,              -- 9-bit read count output
      RDERR => open,                -- 1-bit read error output
      WRCOUNT => open,              -- 9-bit write count output
      WRERR => open,                -- 1-bit write error
      DI => RX_DATA,                -- 64-bit data input
      DIP => par_in,                -- 4-bit parity input
      RDCLK => TX_CLK,              -- 1-bit read clock input
      RDEN => sig_rden,             -- 1-bit read enable input
      RST => reset_both,            -- 1-bit reset input
      WRCLK => RX_CLK,              -- 1-bit write clock input
      WREN => sig_wren              -- 1-bit write enable input
   );

   TX_REM      <= par_out(2 downto 0);
   TX_EOF_N    <= par_out(3);
   TX_SOF_N    <= par_out(4);
   TX_EOP_N    <= par_out(5);
   TX_SOP_N    <= par_out(6);
   TX_SRC_RDY_N <= sig_empty;
   sig_rden    <= not TX_DST_RDY_N;

end architecture full;
