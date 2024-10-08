-- mfb_pd_asfifo_ent.vhd: Asynchronous packet discard FIFO
--
--
-- Copyright (C) 2018 CESNET z. s. p. o.
-- SPDX-License-Identifier: BSD-3-Clause
-- Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

-- library containing log2 function
use work.math_pack.all;
use work.type_pack.all;

-- ----------------------------------------------------------------------------
--                             Description
-- ----------------------------------------------------------------------------
-- Accepts MFB packets and forwards them
-- Setting the RX_DISCARD signal to '1' marks packet on the corresponding RX_MFB_EOF as to be discarded
-- (The RX_DISCARD value is only regarded when the corresponding RX_MFB_EOF is '1')
-- Setting the RX_FORCE_DISCARD signal from '0' to '1' makes the current RX data not to be inserted in the FIFO and delets all data from last EOF (not including the EOF)
-- After returning RX_FORCE_DISCARD back to '0' the next valid data must start with a SOF (the RX_FORCE_RUN can be held for multiple CLK periods until the next SOF)
-- Discarded packets are not forwarded
--
-- THis component is based on the FLU_PRFIFO unit (comp/flu_tools/storage/prfifo)

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------

entity MFB_PD_ASFIFO is
generic (
   -- Numer of items (words) in buffer
   --    (Must be able to hold at least one maximum sized packet plus one word for beginning of next packet)
   ITEMS       : natural := 512;
   -- You can set additional latency of write pointer to read side.
   WR_PTR_ADD_LATENCY : natural := 0;

   -- MFB bus characteristics
   REGIONS     : natural := 4;
   REGION_SIZE : natural := 8;
   BLOCK_SIZE  : natural := 8;
   ITEM_WIDTH  : natural := 8;
   DEVICE      : string  := "ULTRASCALE"
);
port (
   -- RX Synchronization
   RX_CLK           : in  std_logic;
   RX_RESET         : in  std_logic;

   -- RX MFB
   RX_DATA          : in  std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   RX_SOF_POS       : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   RX_EOF_POS       : in  std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   RX_SOF           : in  std_logic_vector(REGIONS-1 downto 0);
   RX_EOF           : in  std_logic_vector(REGIONS-1 downto 0);
   RX_SRC_RDY       : in  std_logic;
   RX_DST_RDY       : out std_logic;
   -- Discard packet on corresponding RX_MFB_EOF
   RX_DISCARD       : in  std_logic_vector(REGIONS-1 downto 0);
   -- Discard currently inserted packet (the packet's SOF has already been sent)
   RX_FORCE_DISCARD : in  std_logic;
   -- Current number of taken items in FIFO (is not precise as this is an asynchronous FIFO) (Clocked on RX_CLK)
   STATUS           : out std_logic_vector(log2(ITEMS+1)-1 downto 0);

   -- TX Synchronization
   TX_CLK           : in  std_logic;
   TX_RESET         : in  std_logic;
   -- RX MFB
   TX_DATA          : out std_logic_vector(REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 downto 0);
   TX_SOF_POS       : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE))-1 downto 0);
   TX_EOF_POS       : out std_logic_vector(REGIONS*max(1,log2(REGION_SIZE*BLOCK_SIZE))-1 downto 0);
   TX_SOF           : out std_logic_vector(REGIONS-1 downto 0);
   TX_EOF           : out std_logic_vector(REGIONS-1 downto 0);
   TX_SRC_RDY       : out std_logic;
   TX_DST_RDY       : in  std_logic

);
end MFB_PD_ASFIFO;
