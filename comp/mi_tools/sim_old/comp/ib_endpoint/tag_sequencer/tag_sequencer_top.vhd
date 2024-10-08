-- tag_sequencer_top.vhd: Two tag sequencers in parallel
-- Copyright (C) 2010 CESNET
-- Author(s): Viktor Pus <pus@liberouter.org>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$
--
-- TODO:
--
--
library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use ieee.std_logic_arith.all;

-- ----------------------------------------------------------------------------
--                        Entity declaration
-- ----------------------------------------------------------------------------
entity TAG_SEQUENCER_TOP is
   generic (
      --+ Width of TAG signals to Endpoint. Has impact on memory depth.
      EP_TAG_WIDTH      : integer := 8;
      --+ Width of TAG signals to user. Has impact on memory width.
      USR_TAG_WIDTH     : integer := 8
   );
   port (
      --+ Common signals
      CLK            : in  std_logic;
      RESET          : in  std_logic;

      --+ UP direction
      USR_TAG        : in  std_logic_vector(USR_TAG_WIDTH-1 downto 0);
      USR_REQ        : in  std_logic;
      USR_ACK        : out std_logic;
      USR_TRANS_TYPE : in  std_logic_vector(1 downto 0); -- G2LR=00, L2GW=01
      EP_TAG         : out std_logic_vector(EP_TAG_WIDTH-1 downto 0);
      EP_REQ         : out std_logic;
      EP_ACK         : in  std_logic;
      EP_TRANS_TYPE  : OUT std_logic_vector(1 downto 0);

      --+ DOWN direction
      EP_OP_TAG      : in  std_logic_vector(EP_TAG_WIDTH-1 downto 0);
      EP_OP_DONE     : in  std_logic;
      USR_OP_TAG     : out std_logic_vector(USR_TAG_WIDTH-1 downto 0);
      USR_OP_DONE    : out std_logic;

      --* Completition buffer is full
      WR_FULL        : out std_logic;
      RD_FULL        : out std_logic;
      --* Completition buffer is empty
      WR_EMPTY       : out std_logic;
      RD_EMPTY       : out std_logic
   );
end entity TAG_SEQUENCER_TOP;

-- ----------------------------------------------------------------------------
--                                 Architecture
-- ----------------------------------------------------------------------------
architecture FULL of TAG_SEQUENCER_TOP is

   constant WR_TAG_WIDTH : integer := 2;

   signal wr_usr_req       : std_logic;
   signal wr_usr_ack       : std_logic;
   signal wr_ep_tag        : std_logic_vector(WR_TAG_WIDTH-1 downto 0);
   signal wr_ep_req        : std_logic;
   signal wr_ep_ack        : std_logic;
   signal wr_ep_trans_type : std_logic_vector(1 downto 0);
   signal wr_ep_op_done    : std_logic;
   signal wr_usr_op_tag    : std_logic_vector(USR_TAG_WIDTH-1 downto 0);
   signal wr_usr_op_done   : std_logic;
   signal wr_pause_in      : std_logic;
   signal wr_pause_out     : std_logic;

   signal rd_usr_req       : std_logic;
   signal rd_usr_ack       : std_logic;
   signal rd_ep_tag        : std_logic_vector(EP_TAG_WIDTH-2 downto 0);
   signal rd_ep_req        : std_logic;
   signal rd_ep_ack        : std_logic;
   signal rd_ep_trans_type : std_logic_vector(1 downto 0);
   signal rd_ep_op_done    : std_logic;
   signal rd_usr_op_tag    : std_logic_vector(USR_TAG_WIDTH-1 downto 0);
   signal rd_usr_op_done   : std_logic;
   signal rd_pause_in      : std_logic;
   signal rd_pause_out     : std_logic;

   signal reg_arbiter      : std_logic;
   signal reg_arbiter_en   : std_logic;

   signal zeros            : std_logic_vector(EP_TAG_WIDTH-1 downto 0);
-- ----------------------------------------------------------------------------
--                        Architecture implementation
-- ----------------------------------------------------------------------------
begin

   zeros <= (others => '0');

   --* Sequencer for WRITE tags
   wr_tag_sequencer : entity work.tag_sequencer
   generic map(
      EP_TAG_WIDTH   => WR_TAG_WIDTH,
      USR_TAG_WIDTH  => USR_TAG_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      USR_TAG        => USR_TAG,
      USR_REQ        => wr_usr_req,
      USR_ACK        => wr_usr_ack,
      USR_TRANS_TYPE => USR_TRANS_TYPE,

      EP_TAG         => wr_ep_tag,
      EP_REQ         => wr_ep_req,
      EP_ACK         => wr_ep_ack,
      EP_TRANS_TYPE  => wr_ep_trans_type,

      EP_OP_TAG      => EP_OP_TAG(WR_TAG_WIDTH downto 1), -- LSB is R/W
      EP_OP_DONE     => wr_ep_op_done,

      USR_OP_TAG     => wr_usr_op_tag,
      USR_OP_DONE    => wr_usr_op_done,

      FULL           => WR_FULL,
      EMPTY          => WR_EMPTY,

      SIBLING_PAUSE_IN => wr_pause_in,
      SIBLING_PAUSE_OUT=> wr_pause_out
   );

   --* Sequencer for READ tags
   rd_tag_sequencer : entity work.tag_sequencer
   generic map(
      EP_TAG_WIDTH   => EP_TAG_WIDTH-1,
      USR_TAG_WIDTH  => USR_TAG_WIDTH
   )
   port map(
      CLK            => CLK,
      RESET          => RESET,

      USR_TAG        => USR_TAG,
      USR_REQ        => rd_usr_req,
      USR_ACK        => rd_usr_ack,
      USR_TRANS_TYPE => USR_TRANS_TYPE,

      EP_TAG         => rd_ep_tag,
      EP_REQ         => rd_ep_req,
      EP_ACK         => rd_ep_ack,
      EP_TRANS_TYPE  => rd_ep_trans_type,

      EP_OP_TAG      => EP_OP_TAG(EP_TAG_WIDTH-1 downto 1), -- LSB is R/W
      EP_OP_DONE     => rd_ep_op_done,

      USR_OP_TAG     => rd_usr_op_tag,
      USR_OP_DONE    => rd_usr_op_done,

      FULL           => RD_FULL,
      EMPTY          => RD_EMPTY,

      SIBLING_PAUSE_IN => rd_pause_in,
      SIBLING_PAUSE_OUT=> rd_pause_out
   );

   -- Requests path
   wr_usr_req <= USR_REQ and USR_TRANS_TYPE(0); -- L2GW or L2LW
   rd_usr_req <= USR_REQ and not USR_TRANS_TYPE(0); -- G2LR or L2LR

   USR_ACK <= wr_usr_ack or rd_usr_ack;

   ep_tag_p : process(rd_ep_tag, wr_ep_tag, rd_ep_req, wr_ep_req,
      wr_ep_trans_type, rd_ep_trans_type)
   begin
      if wr_ep_req = '1' then
         EP_TAG <= zeros(EP_TAG_WIDTH-1 downto WR_TAG_WIDTH+1) &
                   wr_ep_tag & '1'; -- WRITE tags are marked by LSB=1
         EP_TRANS_TYPE <= wr_ep_trans_type;
      else
         EP_TAG <= rd_ep_tag & '0'; -- READ tags are marked by LSB=0
         EP_TRANS_TYPE <= rd_ep_trans_type;
      end if;
   end process;

   EP_REQ <= wr_ep_req or rd_ep_req;

   wr_ep_ack <= EP_ACK and wr_ep_req;
   rd_ep_ack <= EP_ACK and rd_ep_req;

   -- Returning tags path
   wr_ep_op_done <= EP_OP_DONE and EP_OP_TAG(0); -- If tag was marked by LSB=1
   rd_ep_op_done <= EP_OP_DONE and not EP_OP_TAG(0); -- .. marked by LSB=0

   -- R/W returing tags arbitration
   reg_arbiter_p : process(CLK, RESET)
   begin
      if CLK'event and CLK = '1' then
         if RESET = '1' then
            reg_arbiter <= '0';
         else
            if reg_arbiter_en = '1' then
               reg_arbiter <= not reg_arbiter;
            end if;
         end if;
      end if;
   end process;

   arbitration_signals_p : process(reg_arbiter, rd_pause_out, wr_pause_out)
   begin
      reg_arbiter_en <= '0';
      rd_pause_in <= '0';
      wr_pause_in <= '0';

      if rd_pause_out = '1' and wr_pause_out = '1' then -- Arbitration needed
         reg_arbiter_en <= '1';
         rd_pause_in <= reg_arbiter;
         wr_pause_in <= not reg_arbiter;
      end if;
   end process;

   USR_OP_DONE <= wr_usr_op_done or rd_usr_op_done;

   usr_op_tag_p : process(wr_usr_op_done, wr_usr_op_tag, rd_usr_op_tag)
   begin
      if wr_usr_op_done = '1' then
         USR_OP_TAG <= wr_usr_op_tag;
      else
         USR_OP_TAG <= rd_usr_op_tag;
      end if;
   end process;

end architecture FULL;
