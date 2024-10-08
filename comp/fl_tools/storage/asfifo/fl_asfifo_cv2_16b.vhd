-- fl_asfifo_cv2_16b.vhd : Async FL_FIFO composed of one virtex5 built-in FIFO
-- Copyright (C) 2009 CESNET
-- Author(s): Jan Stourac <xstour03@stud.fit.vutbr.cz
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO: There was used 72b fifo for 21b data. It uses one BlockRAM - if
--       you need more space for saved words, you should use smaller fifo.

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_arith.all;
use IEEE.std_logic_unsigned.all;
library unisim;
use unisim.vcomponents.all;

-- ----------------------------------------------------------------------------
--                              Entity declaration
-- ----------------------------------------------------------------------------
entity FL_ASFIFO_CV2_16B is
   port(
      RX_CLK         : in  std_logic;
      TX_CLK         : in  std_logic;
      RX_RESET       : in  std_logic;
      TX_RESET       : in  std_logic;

      RX_DATA        : in  std_logic_vector(15 downto 0);
      RX_REM         : in  std_logic_vector( 0 downto 0);
      RX_SOP_N       : in  std_logic;
      RX_EOP_N       : in  std_logic;
      RX_SOF_N       : in  std_logic;
      RX_EOF_N       : in  std_logic;
      RX_SRC_RDY_N   : in  std_logic;
      RX_DST_RDY_N   : out std_logic;

      TX_DATA        : out std_logic_vector(15 downto 0);
      TX_REM         : out std_logic_vector( 0 downto 0);
      TX_SOP_N       : out std_logic;
      TX_EOP_N       : out std_logic;
      TX_SOF_N       : out std_logic;
      TX_EOF_N       : out std_logic;
      TX_SRC_RDY_N   : out std_logic;
      TX_DST_RDY_N   : in  std_logic
   );
end FL_ASFIFO_CV2_16B;
-- ----------------------------------------------------------------------------
--                              Architecture declaration
-- ----------------------------------------------------------------------------
architecture full of fl_asfifo_cv2_16b is

signal fifo_rx_data : std_logic_vector(31 downto 0);
signal fifo_tx_data : std_logic_vector(31 downto 0);

signal par_in     : std_logic_vector(3 downto 0);
signal par_out    : std_logic_vector(3 downto 0);

signal reset_both : std_logic;

signal sig_empty  : std_logic;
signal sig_full   : std_logic;
signal sig_rden   : std_logic;
signal sig_wren   : std_logic;

begin

   reset_both <= RX_RESET or TX_RESET;

   fifo_rx_data <= "000000000000000" & RX_REM & RX_DATA;

   par_in  <= RX_SOP_N & RX_EOP_N & RX_SOF_N & RX_EOF_N;
   RX_DST_RDY_N <= sig_full;
   sig_wren <= not RX_SRC_RDY_N;

   FIFO18_36_inst : FIFO18_36
   generic map (
      ALMOST_FULL_OFFSET => X"0080",  -- Sets almost full threshold
      ALMOST_EMPTY_OFFSET => X"0080", -- Sets the almost empty threshold
      DO_REG => 1,                    -- Enable output register (0 or 1)
                                      -- Must be 1 if EN_SYN = FALSE
      EN_SYN => FALSE,                -- Specifies FIFO as Asynchronous (FALSE)
                                      -- or Synchronous (TRUE)
      FIRST_WORD_FALL_THROUGH => TRUE,-- Sets the FIFO FWFT to TRUE or FALSE
      SIM_MODE => "SAFE") -- Simulation: "SAFE" vs "FAST", see "Synthesis and Simulation
                          -- Design Guide" for details
   port map (
      ALMOSTEMPTY => open,          -- 1-bit almost empty output flag
      ALMOSTFULL => open,           -- 1-bit almost full output flag
      DO => fifo_tx_data,           -- 32-bit data output
      DOP => par_out,               -- 4-bit parity data output
      EMPTY => sig_empty,           -- 1-bit empty output flag
      FULL => sig_full,             -- 1-bit full output flag
      RDCOUNT => open,              -- 9-bit read count output
      RDERR => open,                -- 1-bit read error output
      WRCOUNT => open,              -- 9-bit write count output
      WRERR => open,                -- 1-bit write error
      DI => fifo_rx_data,           -- 32-bit data input
      DIP => par_in,                -- 4-bit parity input
      RDCLK => TX_CLK,              -- 1-bit read clock input
      RDEN => sig_rden,             -- 1-bit read enable input
      RST => reset_both,            -- 1-bit reset input
      WRCLK => RX_CLK,              -- 1-bit write clock input
      WREN => sig_wren              -- 1-bit write enable input
   );

   TX_REM      <= fifo_tx_data(16 downto 16);
   TX_DATA     <= fifo_tx_data(15 downto 0);

   TX_EOF_N    <= par_out(0);
   TX_SOF_N    <= par_out(1);
   TX_EOP_N    <= par_out(2);
   TX_SOP_N    <= par_out(3);
   TX_SRC_RDY_N <= sig_empty;
   sig_rden    <= not TX_DST_RDY_N;

end architecture full;
