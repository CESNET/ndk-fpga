-- switch_impl_nofifo.vhd: Switch without FIFO (IFNUM is in the first word)
-- Copyright (C) 2010 CESNET
-- Author(s): Jan Viktorin <xvikto03@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

-- Math package - log2 function
use work.math_pack.all;

-- ----------------------------------------------------------------------------
--                        Architecture declaration
-- ----------------------------------------------------------------------------

--* This architecture is intended to save some resouces when the IFNUM is located
--* in the first word of the FrameLink. In that case no special FIFO is needed.
--* Uses only one register for FrameLink data to solve the 1 CLK delay and because
--* of possible waiting for the TX interfaces to be ready.
--*
--* @author Jan Viktorin
architecture nofifo of fl_switch_impl is

   constant REM_WIDTH   : integer := log2(DATA_WIDTH / 8);
   --* Total FrameLink width (contains DATA, REM, SOF, SOP, EOF, EOP signals)
   constant FL_WIDTH : integer := DATA_WIDTH + REM_WIDTH + 4;

   --* Signal that is used to reload the tx_out_array
   signal tx_out_reload : std_logic;
   --* Connects the readed IFNUM and tx_out_array
   signal tx_out_ifnum     : std_logic_vector(TX_COUNT - 1 downto 0);

   --* Register to store all incoming FrameLink data
   signal reg_fl        : std_logic_vector(FL_WIDTH - 1 downto 0);
   signal reg_fl_we     : std_logic;

   --* Enables/disables sending to TX. Needed to be register because
   --* of delay 1 CLK (until sending the readed data)
   signal reg_send_en_n_we : std_logic;
   signal reg_send_en_n    : std_logic;

   --* Register that holds the last IFNUM
   signal reg_ifnum     : std_logic_vector(TX_COUNT - 1 downto 0);
   signal reg_ifnum_we  : std_logic;

   --* Reading from Framelink just now
   signal rx_isreading_n  : std_logic;
   --* IFNUM was read in the current FL word (RX_SOF_N = '0')
   signal rx_read_ifnum_n : std_logic;

begin

   rx_isreading_n <= RX_SRC_RDY_N or not tx_out_reload;
   RX_DST_RDY_N   <= not tx_out_reload;

   rx_read_ifnum_n   <= RX_SOF_N or rx_isreading_n;

   -- IFNUM_MUX:
   tx_out_ifnum   <= IFNUM when rx_read_ifnum_n = '0' else
                     reg_ifnum;


   -- Block of TX_OUT units to solve the TX_SRC/DST_RDY_N logic
   tx_out_array  : entity work.tx_out_array
   generic map (
      TX_COUNT    => TX_COUNT,
      DATA_WIDTH  => DATA_WIDTH
   )
   port map (
      CLK      => CLK,
      RESET    => RESET,
      IFNUM    => tx_out_ifnum,
      SEND_EN_N   => reg_send_en_n,
      RELOAD   => tx_out_reload,
      TX_SRC_RDY_N   => TX_SRC_RDY_N,
      TX_DST_RDY_N   => TX_DST_RDY_N
   );


   -- FrameLink register (REG_FL)
   TX_DATA  <= reg_fl(FL_WIDTH - 1 downto FL_WIDTH - DATA_WIDTH);
   TX_REM   <= reg_fl(FL_WIDTH - DATA_WIDTH - 1 downto FL_WIDTH - DATA_WIDTH - REM_WIDTH);
   TX_SOF_N <= reg_fl(3);
   TX_EOF_N <= reg_fl(2);
   TX_SOP_N <= reg_fl(1);
   TX_EOP_N <= reg_fl(0);

   reg_fl_we   <= tx_out_reload;

   register_fl : process(CLK, reg_fl_we, RX_DATA, RX_REM, RX_SOF_N, RX_EOF_N, RX_SOP_N, RX_EOP_N)
   begin
      if CLK'event and CLK = '1' then
         if reg_fl_we = '1' then
            reg_fl <= RX_DATA & RX_REM & RX_SOF_N & RX_EOF_N & RX_SOP_N & RX_EOP_N;
         end if;
      end if;
   end process;


   -- Register SEND_EN_N (REG_SEND_EN_N)
   reg_send_en_n_we  <= tx_out_reload;

   register_send_en_n : process(CLK, rx_isreading_n, reg_send_en_n_we)
   begin
      if CLK'event and CLK = '1' then
         if reg_send_en_n_we = '1' then
            reg_send_en_n <= rx_isreading_n;
         end if;
      end if;
   end process;


   -- Register IFNUM (REG_IFNUM)
   reg_ifnum_we   <= not rx_read_ifnum_n;

   register_ifnum : process(CLK, reg_ifnum_we)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            -- on reset, disable all TX interfaces
            reg_ifnum <= (others => '0');
         elsif reg_ifnum_we = '1' then
            reg_ifnum <= IFNUM;
         end if;
      end if;
   end process;

end architecture;
