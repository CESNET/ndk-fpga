--
-- lb_endpoint_arch.vhd: Internal Bus End Point Component
-- Copyright (C) 2006 CESNET
-- Author(s): Petr Kobiersky <xkobie00@stud.fit.vutbr.cz>
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
use work.ib_pkg.all; -- Internal Bus package

-- ----------------------------------------------------------------------------
--                      Architecture declaration
-- ----------------------------------------------------------------------------
architecture IB_ENDPOINT_CORE_ARCH of IB_ENDPOINT_CORE is

   -- Input maping
   signal ib_in_data              : std_logic_vector(63 downto 0);
   signal ib_in_src_rdy           : std_logic;
   signal ib_in_sop               : std_logic;
   signal ib_in_eop               : std_logic;
   signal ib_in_dst_rdy           : std_logic;
   signal internal_bus_down       : t_internal_bus_link64;

   -- Output Data
   signal ib_out_sop              : std_logic;
   signal ib_out_eop              : std_logic;
   signal ib_out_src_rdy          : std_logic;
   signal ib_out_dst_rdy          : std_logic;

   -- Address Decoder
   signal addr_dec_sop_vld        : std_logic;
   signal addr_dec_trans_type     : std_logic_vector(3 downto 0);
   signal addr_dec_write_trans    : std_logic;
   signal addr_dec_read_trans     : std_logic;
   signal addr_dec_read_back      : std_logic;

   -- Input Shift Register
   signal input_shr_data_out      : std_logic_vector(63 downto 0);
   signal input_shr_data_out_vld  : std_logic;
   signal input_shr_sop_out       : std_logic;
   signal input_shr_eop_out       : std_logic;
   signal input_shr_shr_re        : std_logic;
   signal input_shr_write_re      : std_logic;
   signal input_shr_read_re       : std_logic;

   -- Write Side Signals
   signal write_addr_we           : std_logic;
   signal write_addr_cnt          : std_logic_vector(ADDR_WIDTH-4 downto 0); -- Not using last 3 bits (always 0)
   signal write_addr_cnt_ce       : std_logic;
   signal write_length_reg        : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
   signal write_length_we         : std_logic;
   signal write_fsm_idle          : std_logic;
   signal write_fsm_init_be       : std_logic;
   signal write_fsm_sof           : std_logic;
   signal write_fsm_eof           : std_logic;
   signal write_fsm_wr_req        : std_logic;


   -- Read Interface Registers
   signal gen_read_req            : std_logic; -- '1' when read request generating (ARDY problem)
   signal read_addr_we            : std_logic;
   signal master_read_addr_we     : std_logic;
   signal read_align_reg          : std_logic_vector(2 downto 0);
   signal read_addr_cnt           : std_logic_vector(ADDR_WIDTH-1 downto 0);
   signal read_lenght_reg         : std_logic_vector(C_IB_LENGTH_WIDTH-1 downto 0);
   signal read_lenght_reg_we      : std_logic;
   signal master_read_lenght_we   : std_logic;
   signal read_tag_reg            : std_logic_vector(15 downto 0);
   signal read_tag_reg_we         : std_logic;
   signal read_dst_addr_reg       : std_logic_vector(31 downto 0);
   signal read_dst_addr_reg_we    : std_logic;
   signal read_src_addr_reg       : std_logic_vector(31 downto 0);
   signal read_fsm_idle           : std_logic;

   signal slave_read_fsm_init_be  : std_logic;
   signal master_read_fsm_init_be : std_logic;
   signal read_fsm_sof            : std_logic;
   signal read_fsm_eof            : std_logic;
   signal master_read_fsm_sof     : std_logic;
   signal master_read_fsm_eof     : std_logic;
   signal master_read_fsm_rd      : std_logic;
   signal read_fsm_rd             : std_logic;

   -- Read Align circuit
   signal slave_read_align_init   : std_logic;
   signal master_read_align_init  : std_logic;
   signal read_align_data_out     : std_logic_vector(63 downto 0);
   signal read_align_src_rdy_out  : std_logic;
   signal read_align_dst_rdy_out  : std_logic;
   signal read_align_eof_out      : std_logic;

   -- Write Align circuit
   signal write_align_data_out    : std_logic_vector(63 downto 0);
   signal write_align_src_rdy_out : std_logic;
   signal write_align_dst_rdy_out : std_logic;
   signal write_align_eof_out     : std_logic;

  -- Data out from read align pipeline
   signal read_data_out           : std_logic_vector(63 downto 0);
   signal read_src_rdy_out        : std_logic;
   signal read_dst_rdy_out        : std_logic;
   signal read_eof_out            : std_logic;

   -- Read Request
   signal re_counter                 : std_logic_vector(12 downto 0);
   signal master_re_counter          : std_logic_vector(12 downto 0);
   signal re_counter_reg             : std_logic_vector(C_IB_LENGTH_WIDTH-3 downto 0);
   signal last_read_req              : std_logic;
   signal master_re_counter_reg      : std_logic_vector(C_IB_LENGTH_WIDTH-3 downto 0);
   signal master_last_read_req       : std_logic;

   -- Header Generator
   signal hdr_data                   : std_logic_vector(63 downto 0);
   signal rd_compl_req               : std_logic;
   signal rd_compl_ack               : std_logic;
   signal get_slave_master           : std_logic;
   signal get_second_hdr             : std_logic;

   -- Upstream Multipexor
   signal upstream_mux               : std_logic_vector(63 downto 0);
   signal upstream_mux_sel           : std_logic;

   signal read_shr_src_rdy_out       : std_logic;
   signal read_shr_dst_rdy_out       : std_logic;
   signal read_shr_data_out          : std_logic_vector(63 downto 0);

   signal rd_compl_start             : std_logic;
   signal rd_compl_done              : std_logic;
   signal read_reset                 : std_logic; -- Reset read part after abort
   signal bm_read_ack                : std_logic;
   signal bm_ack_out                 : std_logic;
   signal get_trans_type             : std_logic_vector(1 downto 0);
   signal gen_bm_op_done             : std_logic;
   signal bm_fsm_idle                : std_logic;
   signal aux_sof                    : std_logic;
   signal aux_eof                    : std_logic;

   -- Bus master length max comparator; BM_LENGTH = 0 is max
   signal cmp_bm_length_max : std_logic;

begin

-- Reset read part of FSM
read_reset <= IB_RESET or RD_WR_ABORT;

-- Read Interface
RD_ADDR <= read_addr_cnt;

-------------------------------------------------------------------------------
-- NO INPUT BUFFER (Only input signal maping)
-------------------------------------------------------------------------------
NO_INPUT_BUFFER_GEN: if (INPUT_BUFFER_SIZE = 0) generate
  ib_in_data        <= IB_DOWN_DATA;
  ib_in_src_rdy     <= not IB_DOWN_SRC_RDY_N; --// and ib_in_dst_rdy;
  ib_in_sop         <= not IB_DOWN_SOP_N;
  ib_in_eop         <= not IB_DOWN_EOP_N;
  IB_DOWN_DST_RDY_N <= not ib_in_dst_rdy;
end generate;

-------------------------------------------------------------------------------
-- WITH INPUT BUFFER
-------------------------------------------------------------------------------
INPUT_BUFFER_GEN: if (INPUT_BUFFER_SIZE > 0) generate
 IB_ENDPOINT_DOWNSTREAM_BUFFER_U : entity work.IB_ENDPOINT_DOWNSTREAM_BUFFER
    generic map (
       ITEMS      => INPUT_BUFFER_SIZE
       )
    port map (
     -- Common Interface
       IB_CLK            => IB_CLK,
       IB_RESET          => IB_RESET,
       IN_DATA           => IB_DOWN_DATA,
       IN_SOP_N          => IB_DOWN_SOP_N,
       IN_EOP_N          => IB_DOWN_EOP_N,
       IN_SRC_RDY_N      => IB_DOWN_SRC_RDY_N,
       IN_DST_RDY_N      => IB_DOWN_DST_RDY_N,
       OUT_DATA          => internal_bus_down.data,
       OUT_SOP_N         => internal_bus_down.sop_n,
       OUT_eop_n         => internal_bus_down.eop_n,
       OUT_SRC_RDY_N     => internal_bus_down.src_rdy_n,
       OUT_DST_RDY_N     => internal_bus_down.dst_rdy_n
    );
  ib_in_data                   <= internal_bus_down.data;
  ib_in_src_rdy                <= not internal_bus_down.src_rdy_n;
  ib_in_sop                    <= not internal_bus_down.sop_n;
  ib_in_eop                    <= not internal_bus_down.eop_n;
  internal_bus_down.dst_rdy_n  <=  not ib_in_dst_rdy;
end generate;

-------------------------------------------------------------------------------
-- INPUT SHIFT REGISTER
-------------------------------------------------------------------------------
-- Read when Read FSM or Write FSM want to read
input_shr_shr_re  <= input_shr_write_re or input_shr_read_re;

IB_ENDPOINT_SHIFT_REG_U : entity work.IB_ENDPOINT_SHIFT_REG
   port map (
      -- Common Interface
      CLK          => IB_CLK,
      RESET        => IB_RESET,

      -- Input Interface
      DATA_IN      => ib_in_data,
      SOP_IN       => ib_in_sop,
      EOP_IN       => ib_in_eop,
      SRC_RDY_IN   => ib_in_src_rdy,
      DST_RDY_IN   => ib_in_dst_rdy,

      --Output Interface
      DATA_OUT     => input_shr_data_out,
      DATA_OUT_VLD => input_shr_data_out_vld,
      SOP_OUT      => input_shr_sop_out,
      EOP_OUT      => input_shr_eop_out,
      SHR_RE       => input_shr_shr_re,

      WRITE_TRANS  => addr_dec_write_trans,
      READ_TRANS   => addr_dec_read_trans,
      READ_BACK    => addr_dec_read_back
      );

-------------------------------------------------------------------------------
-- WRITE Interface mapping
-------------------------------------------------------------------------------
WR_DATA    <= input_shr_data_out;
WR_ADDR    <= write_addr_cnt & "000";
WR_LENGTH  <= write_length_reg;
WR_SOF     <= write_fsm_sof;
WR_EOF     <= write_fsm_eof;
WR_REQ     <= write_fsm_wr_req;

-------------------------------------------------------------------------------
-- WRITE FSM
-------------------------------------------------------------------------------
-- Controls writing and droping transactions
IB_ENDPOINT_WRITE_FSM_U : entity work.IB_ENDPOINT_WRITE_FSM
   generic map (
     STRICT_EN        => STRICT_EN
   )
   port map (
      -- Common Interface
      CLK             => IB_CLK,                 -- Clk
      RESET           => IB_RESET,               -- Reset
      IDLE            => write_fsm_idle,         -- FSM is Idle (For Strict Version)
      READ_FSM_IDLE   => read_fsm_idle,          -- Read FSM is Idle (For Strict Version)
      BM_FSM_IDLE     => bm_fsm_idle,            -- BM FSM Idle

      -- SHR_IN Interface
      DATA_VLD        => input_shr_data_out_vld, -- Data from Shift Reg is valid
      SOP             => input_shr_sop_out,      -- Start of Packet
      EOP             => input_shr_eop_out,      -- End of Packet
      SHR_RE          => input_shr_write_re,     -- Read Data from shift reg

      -- Address Decoder Interface
      WRITE_TRANS     => addr_dec_write_trans,   -- Processing write transactio
      READ_BACK       => addr_dec_read_back,

      -- Reg ctrl
      DST_ADDR_WE     => write_addr_we,          -- Store Addr into addr_cnt and addr_align
      DST_ADDR_CNT_CE => write_addr_cnt_ce,      -- Increment address
      SRC_ADDR_WE     => open,                   -- Store Source Address
      LENGTH_WE       => write_length_we,        -- Store Length
      TAG_WE          => open,                   -- Store TAG register
      INIT_BE         => write_fsm_init_be,      -- Init BE circuit

      -- User Component Interface
      WR_SOF          => write_fsm_sof,          -- Start of frame (Start of transaction)
      WR_EOF          => write_fsm_eof,          -- Ent of frame (End of Transaction)
      WR_REQ          => write_fsm_wr_req,       -- Write to user component
      WR_RDY          => WR_RDY,                 -- User component is ready
      RD_BACK         => RD_BACK
   );

-------------------------------------------------------------------------------
-- ADDRESS COUNTER REGISTER
-------------------------------------------------------------------------------
write_addr_cntp: process(IB_RESET, IB_CLK)
begin
   if (IB_CLK'event AND IB_CLK = '1') then
     if (write_addr_cnt_ce = '1') then
       write_addr_cnt <= write_addr_cnt + 1;
     end if;
     if (write_addr_we = '1') then
       write_addr_cnt <= input_shr_data_out(ADDR_WIDTH+31 downto 35);
     end if;
   end if;
end process;

-------------------------------------------------------------------------------
-- LENGTH REGISTER
-------------------------------------------------------------------------------
write_length_regp: process(IB_RESET, IB_CLK)
begin
   if (IB_CLK'event AND IB_CLK = '1') then
     if (write_length_we = '1') then
       write_length_reg <= input_shr_data_out(C_IB_LENGTH_WIDTH-1 downto 0);
     end if;
   end if;
end process;

-------------------------------------------------------------------------------
-- WRITE BE generation
-------------------------------------------------------------------------------
IB_ENDPOINT_BE_WR_U : entity work.IB_ENDPOINT_BE
   port map (
      -- Common Interface
      CLK       => IB_CLK,
      RESET     => IB_RESET,
      -- Control Interface
      SLAVE_INIT      => write_fsm_init_be,
      SLAVE_LENGHT    => input_shr_data_out(2 downto 0),
      SLAVE_ALIGN     => input_shr_data_out(34 downto 32),
      MASTER_INIT     => '0', -- Used only in RD_REQ BE
      MASTER_LENGHT   => "000", -- Used only in RD_REQ BE
      MASTER_ALIGN    => "000", -- Used only in RD_REQ BE
      SOF       => write_fsm_sof,
      EOF       => write_fsm_eof,
      -- Output Interface
      BE        => WR_BE
      );




-------------------------------------------------------------------------------

-------------------------------------------------------------------------------
-- READ PART OF IB_ENDPOINT, ALSO CONTAINS BUSMASTER PART
-------------------------------------------------------------------------------

-------------------------------------------------------------------------------





-------------------------------------------------------------------------------
-- READ FSM
-------------------------------------------------------------------------------
-- Controls reading, generate read signals, controls signals to read registers
IB_ENDPOINT_READ_FSM_U : entity work.IB_ENDPOINT_READ_FSM
   generic map (
     STRICT_EN         => STRICT_EN
   )
   port map (
      -- Common Interface
      CLK              => IB_CLK,
      RESET            => read_reset,     -- IB_RESET,
      IDLE             => read_fsm_idle,  -- FSM is Idle (For Strict Version)
      WRITE_FSM_IDLE   => write_fsm_idle, -- Write FSM is Idle (For Strict Version)

      -- SHR_IN Interface
      DATA_VLD         => input_shr_data_out_vld, -- Input shift reg data signals
      SOP              => input_shr_sop_out,
      SHR_RE           => input_shr_read_re,

      -- Address Decoder Interface
      READ_TRANS       => addr_dec_read_trans,

      -- Component status interface
      LAST_READ_REQ    => last_read_req,     -- Last Read Req

      -- Register control interface
      ADDR_WE          => read_addr_we,         -- Write enable for address counter and align
      TAG_WE           => read_tag_reg_we,      -- Write Tag
      LENGHT_WE        => read_lenght_reg_we,   -- Lenght Write enable
      DST_ADDR_WE      => read_dst_addr_reg_we, -- Store dst_addr into register
      -- Component Init interface
      INIT_BE          => slave_read_fsm_init_be, -- Init BE circuit
      READ_ALIGN_INIT  => slave_read_align_init,
      RD_COMPL_REQ     => rd_compl_req,      -- RD Completition Req
      RD_COMPL_ACK     => rd_compl_ack,      -- RD Completition Ack
      -- Read Interface
      RD_SOF_IN        => read_fsm_sof, -- Start of frame (Start of transaction)
      RD_EOF_IN        => read_fsm_eof, -- Ent of frame (End of Transaction)
      RD_REQ           => read_fsm_rd,  -- Read Enable
      RD_ARDY          => RD_ARDY       -- Adress RDY
   );

RD_SOF_IN    <= read_fsm_sof or master_read_fsm_sof;
RD_EOF_IN    <= read_fsm_eof or master_read_fsm_eof;
RD_REQ       <= read_fsm_rd  or master_read_fsm_rd;
gen_read_req <= read_fsm_rd  or master_read_fsm_rd;
aux_sof      <= read_fsm_sof or master_read_fsm_sof;
aux_eof      <= read_fsm_eof or master_read_fsm_eof;
-------------------------------------------------------------------------------
-- LAST READ REQ GENERATION
-------------------------------------------------------------------------------

last_read_req          <= '1' when (re_counter_reg        = 1) else '0';
master_last_read_req   <= '1' when (master_re_counter_reg = 1) else '0';
re_counter             <= ('0' & input_shr_data_out(11 downto 0)) + input_shr_data_out(34 downto 32) + 7;
master_re_counter      <= (cmp_bm_length_max & BM_LENGTH) + BM_LOCAL_ADDR(2 downto 0) + 7;


-- BUGFIX
-- This is to prevenet 13b counter overflow in case BM_LENGTH = 0 which is to
-- transfer maximal value. In this case, 2xBM_LENGTH maximal value was read from
-- the compontent connected to this endpoint (master_re_counter underflow).
cmp_bm_length_max      <= '1' when BM_LENGTH = conv_std_logic_vector(0, BM_LENGTH'length)
                         else '0';

-- register re_counter_reg ----------------------------------------------------
re_counter_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_lenght_reg_we = '1') then
      re_counter_reg <= re_counter(12 downto 3);
    end if;
    if (RD_ARDY = '1' and gen_read_req = '1') then
      re_counter_reg <= re_counter_reg - 1;
    end if;
  end if;
end process;

-- register master_re_counter_reg ---------------------------------------------
master_counter_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (master_read_lenght_we = '1') then
      master_re_counter_reg <= master_re_counter(12 downto 3);
    end if;
    if (RD_ARDY = '1' and gen_read_req = '1') then
      master_re_counter_reg <= master_re_counter_reg - 1;
    end if;
  end if;
end process;


-------------------------------------------------------------------------------
-- READ REGISTERS
-------------------------------------------------------------------------------

-- register read_lenght_reg ---------------------------------------------------
read_lenght_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_lenght_reg_we = '1') then
      read_lenght_reg <= input_shr_data_out(C_IB_LENGTH_WIDTH-1 downto 0);
    end if;
  end if;
end process;

-- register read_tag_reg ------------------------------------------------------
-- Used in slave mode only
read_tag_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_tag_reg_we = '1') then
      read_tag_reg <= input_shr_data_out(31 downto 16);
    end if;
  end if;
end process;

-- register read_dst_addr_reg -------------------------------------------------
-- Used in slave mode only
read_dst_addr_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_dst_addr_reg_we = '1') then
      read_dst_addr_reg <= input_shr_data_out(31 downto 0);
    end if;
  end if;
end process;


-- register read_src_addr_reg -------------------------------------------------
read_src_addr_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_addr_we = '1') then
      read_src_addr_reg <= input_shr_data_out(63 downto 32);
    end if;
  end if;
end process;


-- register read_align_reg ----------------------------------------------------
-- Used both in master or slave mode
read_align_regp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (read_addr_we = '1') then
      read_align_reg <= input_shr_data_out(34 downto 32);
    end if;
    if (master_read_addr_we = '1') then
      read_align_reg <= BM_LOCAL_ADDR(2 downto 0);
    end if;
  end if;
end process;

-- read_addr_cnt counter ------------------------------------------------------
-- Used both in master or slave mode
read_addr_cntp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (RD_ARDY = '1' and gen_read_req = '1') then
      read_addr_cnt <= read_addr_cnt + 8;
    end if;
    if (read_addr_we = '1') then
      read_addr_cnt <= input_shr_data_out(ADDR_WIDTH+31 downto 35) & "000";
    end if;
    if (master_read_addr_we = '1') then
      read_addr_cnt <= BM_LOCAL_ADDR(ADDR_WIDTH-1 downto 3) & "000";
    end if;
  end if;
end process;


-------------------------------------------------------------------------------
-- READ BE generation
-------------------------------------------------------------------------------
IB_ENDPOINT_BE_RD_U : entity work.IB_ENDPOINT_BE
   port map (
      -- Common Interface
      CLK       => IB_CLK,
      RESET     => read_reset, --IB_RESET,
      -- Control Interface
      SLAVE_INIT      => slave_read_fsm_init_be,
      SLAVE_LENGHT    => input_shr_data_out(2 downto 0),
      SLAVE_ALIGN     => input_shr_data_out(34 downto 32),
      MASTER_INIT     => master_read_fsm_init_be,
      MASTER_LENGHT   => BM_LENGTH(2 downto 0),
      MASTER_ALIGN    => BM_LOCAL_ADDR(2 downto 0),
      SOF             => aux_sof,
      EOF             => aux_eof,
      -- Output Interface
      BE              => RD_BE
      );

-------------------------------------------------------------------------------
-- READ BUFFER
-------------------------------------------------------------------------------
IB_ENDPOINT_READ_SHR_U : entity work.IB_ENDPOINT_READ_SHR
   generic map (
      DATA_WIDTH     => 64
      )
   port map (
      -- Common Interface
      CLK             => IB_CLK,
      RESET           => read_reset, --IB_RESET,
      -- Input Interface
      RD_DATA_IN      => RD_DATA,
      RD_SRC_RDY_IN   => RD_SRC_RDY,
      RD_DST_RDY_IN   => RD_DST_RDY,
      -- Output Interface
      RD_DATA_OUT     => read_shr_data_out,
      RD_SRC_RDY_OUT  => read_shr_src_rdy_out,
      RD_DST_RDY_OUT  => read_shr_dst_rdy_out
      );

-------------------------------------------------------------------------------
-- READ ALIGN REGISTER
-------------------------------------------------------------------------------
IB_ENDPOINT_READ_ALIGN_U : entity work.IB_ENDPOINT_READ_ALIGN
   port map (
      -- Common Interface
      CLK            => IB_CLK,
      RESET          => read_reset, --IB_RESET,

      -- RD_DATA Interface
      RD_DATA_IN     => read_shr_data_out,
      RD_SRC_RDY_IN  => read_shr_src_rdy_out,
      RD_DST_RDY_IN  => read_shr_dst_rdy_out,

      -- Internal Bus Interface
      RD_DATA_OUT    => read_align_data_out,
      RD_SRC_RDY_OUT => read_align_src_rdy_out,
      RD_DST_RDY_OUT => read_align_dst_rdy_out,
      RD_EOF         => read_align_eof_out,

      -- Align Control Interface
      SLAVE_INIT      => slave_read_align_init,
      SLAVE_LENGTH    => input_shr_data_out(11 downto 0),
      SLAVE_ALIGN     => input_shr_data_out(34 downto 32),
      MASTER_INIT     => master_read_align_init,
      MASTER_LENGTH   => BM_LENGTH,
      MASTER_ALIGN    => BM_LOCAL_ADDR(2 downto 0),
      ALIGN_REG       => read_align_reg
      );


-------------------------------------------------------------------------------
-- WRITE ALIGN REGISTER
-------------------------------------------------------------------------------
WRITE_ALIGN_GEN: if WRITE_REORDER_BUFFER generate
IB_ENDPOINT_WRITE_ALIGN_U : entity work.IB_ENDPOINT_WRITE_ALIGN
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => read_reset, --IB_RESET,
      -- Input Interface
      RD_DATA_IN         => read_align_data_out,
      RD_SRC_RDY_IN      => read_align_src_rdy_out,
      RD_DST_RDY_IN      => read_align_dst_rdy_out,
      RD_EOF_IN          => read_align_eof_out,
      -- Internal Bus Interface
      RD_DATA_OUT        => write_align_data_out,
      RD_SRC_RDY_OUT     => write_align_src_rdy_out,
      RD_DST_RDY_OUT     => write_align_dst_rdy_out,
      RD_EOF_OUT         => write_align_eof_out,

      -- Align Control Interface
      MASTER_ALIGN       => BM_GLOBAL_ADDR(2 downto 0),
      MASTER_LENGTH      => BM_LENGTH(2 downto 0),
      MASTER_INIT        => master_read_align_init,
      SLAVE_ALIGN        => input_shr_data_out(2 downto 0),
      SLAVE_ALIGN_VLD    => read_dst_addr_reg_we,
      SLAVE_LENGTH       => input_shr_data_out(2 downto 0),
      SLAVE_LENGTH_VLD   => read_lenght_reg_we,
      SLAVE_INIT         => slave_read_align_init
      );
end generate;

WRITE_ALIGN_GEN_NOT: if not WRITE_REORDER_BUFFER generate
  write_align_data_out    <= read_align_data_out;
  write_align_src_rdy_out <= read_align_src_rdy_out;
  read_align_dst_rdy_out  <= write_align_dst_rdy_out;
  write_align_eof_out     <= read_align_eof_out;
end generate;

-- Data out from read align pipeline
read_data_out            <= write_align_data_out;
read_src_rdy_out         <= write_align_src_rdy_out;
write_align_dst_rdy_out  <= read_dst_rdy_out;
read_eof_out             <= write_align_eof_out;

-------------------------------------------------------------------------------
-- HEADER GENERATOR
-------------------------------------------------------------------------------
SLAVE_HDR: if not MASTER_EN generate
IB_ENDPOINT_HDR_GEN_U : entity work.IB_ENDPOINT_HDR_GEN_SLAVE
   port map (
      -- Slave Interface
      RD_COMPL_DST_ADDR     => read_dst_addr_reg,
      RD_COMPL_SRC_ADDR     => read_src_addr_reg,
      RD_COMPL_TAG          => read_tag_reg,
      RD_COMPL_LENGTH       => read_lenght_reg,
      -- Control
      GET_SECOND_HDR        => get_second_hdr,
      -- Output Interface
      HEADER_DATA           => hdr_data
      );
end generate;

MASTER_HDR: if MASTER_EN generate
IB_ENDPOINT_HDR_GEN_U : entity work.IB_ENDPOINT_HDR_GEN_MASTER
   port map (
      -- Slave Interface
      RD_COMPL_DST_ADDR  => read_dst_addr_reg,
      RD_COMPL_SRC_ADDR  => read_src_addr_reg,
      RD_COMPL_TAG       => read_tag_reg,
      RD_COMPL_LENGTH    => read_lenght_reg,
      -- Master Interface
      MASTER_GLOBAL_ADDR => BM_GLOBAL_ADDR,
      MASTER_LOCAL_ADDR  => BM_LOCAL_ADDR,
      MASTER_TAG         => BM_TAG,
      MASTER_LENGTH      => BM_LENGTH,
      -- Control
      GET_SLAVE_MASTER   => get_slave_master, -- 0-Slave/1-Master
      GET_SECOND_HDR     => get_second_hdr,  -- Get second header
      GET_TRANS_TYPE     => get_trans_type,
      -- Output Interface
      HEADER_DATA        => hdr_data
      );
end generate;

-------------------------------------------------------------------------------
-- HEADER X DATA MULTIPLEXOR
-------------------------------------------------------------------------------

-- multiplexor upstream_mux ---------------------------------------------------
upstream_muxp: process(upstream_mux_sel, hdr_data, read_data_out)
  begin
  case upstream_mux_sel is
     when '0' => upstream_mux <= hdr_data;
     when '1' => upstream_mux <= read_data_out;
     when others => upstream_mux <= (others => 'X');
  end case;
end process;

-------------------------------------------------------------------------------
-- UPSTREAM FSM
-------------------------------------------------------------------------------
SLAVE_FSM: if not MASTER_EN generate
IB_ENDPOINT_UPSTREAM_FSM_U : entity work.IB_ENDPOINT_UPSTREAM_FSM_SLAVE
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => read_reset,          -- Read Reset
      -- Upstream FSM Request Interface
      RD_COMPL_REQ       => rd_compl_req,
      RD_COMPL_ACK       => rd_compl_ack,
      -- Header Generator Control Interface
      GET_SECOND_HDR     => get_second_hdr,
      -- Align Buffer Interface
      RD_SRC_RDY         => read_src_rdy_out,  -- Align buffer Data Valid
      RD_DST_RDY         => read_dst_rdy_out,  -- Align buffer dst_rdy
      RD_EOF             => read_eof_out,      -- Align buffer Last Data
      -- Multipexor Interface
      MUX_SEL            => upstream_mux_sel,    -- Select HEADER/DATA
      -- Upstream Interface
      SOP                => ib_out_sop,          -- Start of Packet (Start of transaction)
      EOP                => ib_out_eop,          -- Ent of Packet (End of Transaction)
      SRC_RDY            => ib_out_src_rdy,      -- Source Ready
      DST_RDY            => ib_out_dst_rdy       -- Destination Ready
      );
end generate;



MASTER_FSM: if MASTER_EN generate
IB_ENDPOINT_UPSTREAM_FSM_U : entity work.IB_ENDPOINT_UPSTREAM_FSM_MASTER
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => IB_RESET,
      -- Upstream FSM Request Interface
      RD_COMPL_REQ       => rd_compl_req,
      RD_COMPL_ACK       => rd_compl_ack,
      BM_REQ             => BM_REQ,
      BM_READ_ACK        => bm_read_ack,
      BM_ACK             => bm_ack_out,
      BM_TRANS_TYPE      => BM_TRANS_TYPE,
      -- Header Generator Control Interface
      GET_SLAVE_MASTER   => get_slave_master,  -- 0-Slave/1-Master
      GET_SECOND_HDR     => get_second_hdr,    -- Get second header
      GET_TRANS_TYPE     => get_trans_type,
      -- Align buffer Interface
      RD_SRC_RDY         => read_src_rdy_out,  -- Align buffer Data Valid
      RD_DST_RDY         => read_dst_rdy_out,  -- Align buffer dst_rdy
      RD_EOF             => read_eof_out,      -- Align buffer Last Data
      -- Multipexor Interface
      MUX_SEL            => upstream_mux_sel,    -- Select HEADER/DATA
      -- Upstream Interface
      SOP                => ib_out_sop,          -- Start of Packet (Start of transaction)
      EOP                => ib_out_eop,          -- Ent of Packet (End of Transaction)
      SRC_RDY            => ib_out_src_rdy,      -- Source Ready
      DST_RDY            => ib_out_dst_rdy       -- Destination Ready
      );
BM_ACK <= bm_ack_out;
end generate;

-------------------------------------------------------------------------------
--                            BUSMASTER FSM
-------------------------------------------------------------------------------
NOT_BUSMASTER_FSM: if not MASTER_EN generate
   master_read_addr_we      <= '0';
   master_read_lenght_we    <= '0';
   master_read_fsm_sof      <= '0';
   master_read_fsm_eof      <= '0';
   master_read_fsm_rd       <= '0';
   master_read_align_init   <= '0';
   master_read_fsm_init_be  <= '0';
   bm_fsm_idle              <= '1';
end generate;

BUSMASTER_FSM: if MASTER_EN generate


IB_ENDPOINT_MASTER_FSM_U : entity work.IB_ENDPOINT_MASTER_FSM
   generic map (
      STRICT_EN          => STRICT_EN
   )
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => IB_RESET,
      IDLE               => bm_fsm_idle,         -- FSM is Idle (For Strict Version)
      WRITE_FSM_IDLE     => write_fsm_idle,          -- Read FSM is Idle (For Strict Version)

      -- BusMaster Interface
      BM_REQ             => BM_REQ, -- Busmaster Request
      BM_ACK             => bm_ack_out,
      BM_READ_ACK        => bm_read_ack, -- Direction Global to Local/Local to Global
      BM_TRANS_TYPE      => BM_TRANS_TYPE,

      -- Component status interface
      LAST_READ_REQ      => master_last_read_req, -- Last Read Req

      -- Register control interface
      ADDR_WE            => master_read_addr_we,   -- Store Addr into addr_cnt and addr_align
      LENGHT_WE          => master_read_lenght_we, -- Store lenght for Align circuit

      -- Component Init interface
      INIT_BE            => master_read_fsm_init_be,  -- Init BE circuit
      READ_ALIGN_INIT    => master_read_align_init,   -- Init Read Align circuit

      -- Read Interface
      RD_SOF_IN          => master_read_fsm_sof,  -- Start of frame (Start of transaction)
      RD_EOF_IN          => master_read_fsm_eof,  -- Ent of frame (End of Transaction)
      RD_REQ             => master_read_fsm_rd,   -- Read from User Component
      RD_ARDY            => RD_ARDY               -- Adress RDY
);

-------------------------------------------------------------------------------
--                        BM OPERATION DONE BUFFER
-------------------------------------------------------------------------------
rd_compl_start  <= '1' when input_shr_sop_out = '1' and input_shr_shr_re='1' and
                   input_shr_data_out(14 downto 12) = C_IB_RD_COMPL_TRANSACTION and
                   input_shr_data_out(15) = '1' else '0'; -- Flag must be '1' last fragment

rd_compl_done   <= input_shr_eop_out and input_shr_write_re;

-- Local to Local Write or Local to Global Write
gen_bm_op_done <= bm_ack_out and BM_TRANS_TYPE(0);


IB_ENDPOINT_OP_DONE_BUFFER_U: entity work.IB_ENDPOINT_OP_DONE_BUFFER
   port map (
      -- Common Interface
      CLK                => IB_CLK,
      RESET              => IB_RESET,
      -- Read completition tag
      RD_COMPL_TAG       => input_shr_data_out(31 downto 16),
      RD_COMPL_START     => rd_compl_start,   -- Completition transaction goes for processing
      RD_COMPL_DONE      => rd_compl_done,    -- Some write/completition transaction is done
      -- Busmaster Tag
      BM_TAG             => BM_TAG,
      BM_DONE            => gen_bm_op_done,
      -- OP Done Interface
      OP_TAG             => BM_OP_TAG,
      OP_DONE            => BM_OP_DONE
      );

end generate;


-------------------------------------------------------------------------------
--                          OUTPUT REGISTERS
-------------------------------------------------------------------------------
-- Output registers for Internal Bus Output Interface
output_registersp: process(IB_RESET, IB_CLK)
begin
  if (IB_CLK'event AND IB_CLK = '1') then
    if (IB_RESET = '1') then
      IB_UP_SOP_N        <= '1';
      IB_UP_EOP_N        <= '1';
      IB_UP_SRC_RDY_N    <= '1';
    elsif (IB_UP_DST_RDY_N = '0') then
      IB_UP_DATA      <= upstream_mux;
      IB_UP_SOP_N     <= not ib_out_sop; -- Active in Low
      IB_UP_EOP_N     <= not ib_out_eop; -- Active in Low
      IB_UP_SRC_RDY_N <= not ib_out_src_rdy; -- Active in Low
    end if;
  end if;
end process;

ib_out_dst_rdy  <= not IB_UP_DST_RDY_N; -- Active in Low

end architecture IB_ENDPOINT_CORE_ARCH;
