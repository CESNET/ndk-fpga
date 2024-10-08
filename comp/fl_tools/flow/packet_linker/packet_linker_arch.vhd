--
-- packet_linker_ent.vhd: Packet linker component for Frame link
-- Copyright (C) 2007 CESNET
-- Author(s): Vlastimil Kosar <xkosar02@stud.fit.vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause
--
-- $Id$


library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.std_logic_unsigned.all;
use IEEE.std_logic_arith.all;

architecture packet_linker_arch of packet_linker is
  type states is (SREAD, SLINK, SWAIT, SLAST, SINTERNAL);

  signal inner_data      : std_logic_vector(31 downto 0);
  signal inner_rem       : std_logic_vector(1 downto 0);
  signal inner_sof_n     : std_logic;
  signal inner_sop_n     : std_logic;
  signal inner_eop_n     : std_logic;
  signal inner_eof_n     : std_logic;
  signal inner_src_rdy_n : std_logic;
  signal inner_dst_rdy_n : std_logic;

  signal out_data      : std_logic_vector(31 downto 0);
  signal out_rem       : std_logic_vector(1 downto 0);
  signal out_sof_n     : std_logic;
  signal out_sop_n     : std_logic;
  signal out_eop_n     : std_logic;
  signal out_eof_n     : std_logic;
  signal out_src_rdy_n : std_logic;
  signal out_dst_rdy_n : std_logic;

  signal rst   : std_logic;
  signal inc  : std_logic;
  signal count : std_logic_vector(3 downto 0);

  signal data0 : std_logic_vector(31 downto 0);
  signal data1 : std_logic_vector(31 downto 0);
  signal data2 : std_logic_vector(31 downto 0);
  signal data3 : std_logic_vector(31 downto 0);

  signal sdata0 : std_logic_vector(31 downto 0);
  signal sdata1 : std_logic_vector(31 downto 0);
  signal sdata2 : std_logic_vector(31 downto 0);
  signal sdata3 : std_logic_vector(31 downto 0);

  signal shifted_data : std_logic_vector(31 downto 0);

  signal mux_ds_select   : std_logic_vector(1 downto 0);
  signal mux_link_select : std_logic_vector(1 downto 0);

  signal current_state : states;
  signal next_state    : states;

  signal is_last : std_logic;

  signal WE : std_logic;
  signal WEO : std_logic;
  signal WES : std_logic;

  signal reg_rem : std_logic_vector(1 downto 0);
  signal next_rem : std_logic_vector(1 downto 0);

  signal lout_rem : std_logic_vector(1 downto 0);
  signal wout_rem : std_logic_vector(1 downto 0);

  signal wrem_sel : std_logic_vector(3 downto 0);
  signal lrem_sel : std_logic_vector(3 downto 0);

  signal reg_first : std_logic;
  signal next_first : std_logic;

  begin
  -- write enabled registers for data and rem signal
  data_register: process (CLK, RESET)
  begin
    if RESET = '1' then
      inner_sof_n <= '1';
      inner_sop_n <= '1';
      inner_eop_n <= '1';
      inner_eof_n <= '1';
      inner_data <= (others => '0');
      inner_rem  <= (others => '0');
    elsif CLK'event and CLK = '1' then
      if WE = '1' then
        inner_sof_n <= RX_SOF_N;
        inner_sop_n <= RX_SOP_N;
        inner_eop_n <= RX_EOP_N;
        inner_eof_n <= RX_EOF_N;
        inner_data <= RX_DATA;
        inner_rem  <= RX_REM;
      end if;
    end if;
  end process data_register;

  WE <= not (RX_SRC_RDY_N or inner_dst_rdy_n);

  --registers for SOF_N, SOP_N, EOP_N, EOF_N, SRC_RDY_N and DST_RDY_N signal
  data_register2: process (CLK, RESET)
  begin
    if RESET = '1' then
      TX_DATA <= (others => '0');
      TX_REM  <= (others => '0');
      TX_SOF_N <= '1';
      TX_SOP_N <= '1';
      TX_EOP_N <= '1';
      TX_EOF_N <= '1';
    elsif CLK'event and CLK = '1' then
      if WEO = '1' then
        TX_DATA <= out_data;
        TX_REM  <= out_rem;
	TX_SOF_N <= out_sof_n;
        TX_SOP_N <= out_sop_n;
        TX_EOP_N <= out_eop_n;
        TX_EOF_N <= out_eof_N;
      end if;
    end if;
  end process data_register2;

  WEO <= not (out_src_rdy_n or TX_DST_RDY_N);

  data_register3: process (CLK, RESET)
  begin
    if RESET = '1' then
      inner_src_rdy_n <= '1';
      TX_SRC_RDY_N <= '1';
    elsif CLK'event and CLK = '1' then
      if WES = '1' then
        inner_src_rdy_n <= RX_SRC_RDY_N;
        TX_SRC_RDY_N <= out_src_rdy_n;
      end if;
    end if;
  end process data_register3;

  WES <= not out_dst_rdy_n;

  out_dst_rdy_n <= TX_DST_RDY_N;
  inner_dst_rdy_n <= out_dst_rdy_n;

  -- part of packet counter
  packet_counter: process (CLK, rst)
  begin
   if CLK='1' and CLK'event then
     if rst='1' then
        count <= "0001";
     elsif inc='1' then
          count <= count + 1;
     end if;
   end if;
   end process packet_counter;

-- counter control logic
   rst <= not inner_eof_n or RESET;
   inc <= not inner_eop_n and not inner_src_rdy_n and not TX_DST_RDY_N;

  -- variants of data shift
  data0 <= inner_data;
  data1 <= X"00" & inner_data(31 downto 8);
  data2 <= X"0000" & inner_data(31 downto 16);
  data3 <= X"000000" & inner_data(31 downto 24);

  -- multiplexor which shifts bytes to right about 0 to 3 positions
  mux_data_shift: process (mux_ds_select, data0, data1, data2, data3)
  begin
    case mux_ds_select is
      when "11" => shifted_data <= data0;
      when "10" => shifted_data <= data1;
      when "01" => shifted_data <= data2;
      when "00" => shifted_data <= data3;
      when others => null;
    end case;
  end process mux_data_shift;

  -- variants of data link
  sdata0 <= shifted_data;
  sdata1 <= RX_DATA(7 downto 0) & shifted_data(23 downto 0);
  sdata2 <= RX_DATA(15 downto 0) & shifted_data(15 downto 0);
  sdata3 <= RX_DATA(23 downto 0) & shifted_data(7 downto 0);

  -- multiplexor which select one variant of linked data
  mux_link: process (mux_link_select, sdata0, sdata1, sdata2, sdata3)
  begin
    case mux_link_select is
      when "11" => out_data <= sdata0;
      when "10" => out_data <= sdata1;
      when "01" => out_data <= sdata2;
      when "00" => out_data <= sdata3;
      when others => null;
    end case;
  end process mux_link;

  is_last <= (RX_REM(1) and RX_REM(0)) or (reg_rem(1) and reg_rem(0)) or (RX_REM(1) and reg_rem(1)) or (RX_REM(0) and reg_rem(1)) or (RX_REM(1) and reg_rem(0));

  register_rem: process (CLK, RESET)
  begin
     if RESET = '1' then
        reg_rem <= "11";
     elsif CLK'event and CLK = '1' then
        reg_rem <= next_rem;
     end if;
  end process register_rem;

  register_first: process (CLK, RESET)
  begin
     if RESET = '1' then
        reg_first <= '0';
     elsif CLK'event and CLK = '1' then
        reg_first <= next_first;
     end if;
  end process register_first;

  wrem_sel <= reg_rem&RX_REM;
  lrem_sel <= reg_rem&inner_rem;

  wrem_gen:process(wrem_sel)
  begin
     case wrem_sel is
        when "0000" => wout_rem <= "01";
        when "0001" => wout_rem <= "10";
        when "0010" => wout_rem <= "11";
        when "0100" => wout_rem <= "10";
        when "0101" => wout_rem <= "11";
        when "1000" => wout_rem <= "11";
        when others => wout_rem <= "11";
     end case;
  end process wrem_gen;

  lrem_gen:process(lrem_sel)
  begin
     case lrem_sel is
        when "0011" => lout_rem <= "00";
        when "0110" => lout_rem <= "00";
        when "0111" => lout_rem <= "01";
        when "1001" => lout_rem <= "00";
        when "1010" => lout_rem <= "01";
        when "1011" => lout_rem <= "10";
        when "1100" => lout_rem <= "00";
        when "1101" => lout_rem <= "01";
        when "1110" => lout_rem <= "10";
        when "1111" => lout_rem <= "11";
        when others => lout_rem <= "11";
     end case;
  end process lrem_gen;


  -- FA state register
  state_register: process (RESET, CLK)
  begin
    if RESET = '1' then
      current_state <= SREAD;
    elsif CLK'event and CLK = '1' then
      current_state <= next_state;
    end if;
  end process state_register;

  -- transitions in FA
  transitions_FA: process (current_state, inner_src_rdy_n, out_dst_rdy_n, inner_eop_n,
                           inner_eof_n, RX_SRC_RDY_N, RX_EOP_N, is_last, count, inner_rem, reg_rem)
  begin
    case current_state is
      when SREAD =>
                   if inner_src_rdy_n = '0' and out_dst_rdy_n = '0' and count = PACKET_ID and inner_eop_n = '0' and inner_eof_n = '1' then
		      if inner_rem = "11" then
		        next_state <= SLINK;
		      else
                         if RX_SRC_RDY_N = '0' then
                            if RX_EOP_N = '0' then
                               if is_last = '0' then
                                 next_state <= SWAIT;
                               else
                                 next_state <= SLAST;
                               end if;
                            else
                               next_state <= SLINK;
                            end if;
                         else
                            next_state <= SINTERNAL;
                         end if;
		      end if;
                   else
                      next_state <= current_state;
                   end if;
      when SLINK =>
                   if inner_src_rdy_n = '0' and out_dst_rdy_n = '0' then
		      if reg_rem = "11" then
		        if inner_eop_n = '0' then
			   next_state <= SREAD;
	                else
			   next_state <= current_state;
		        end if;
		      else
                         if RX_SRC_RDY_N = '0' then
                            if RX_EOP_N = '0' then
                               if is_last = '0' then
                                  next_state <= SWAIT;
                               else
                                  next_state <= SLAST;
                               end if;
                            else
                               next_state <= current_state;
                            end if;
                         else
                            next_state <= SINTERNAL;
                         end if;
		      end if;
                   else
                      next_state <= current_state;
                   end if;
      when SLAST =>
                   if out_dst_rdy_n = '0' then
                      next_state <= SREAD;
                   else
                      next_state <= current_state;
                   end if;
      when SWAIT =>
                   if out_dst_rdy_n = '0' then
                      next_state <= SREAD;
		   else
		      next_state <= current_state;
		   end if;
      when SINTERNAL =>
                       if RX_SRC_RDY_N = '0' and out_dst_rdy_n = '0' then
                          if RX_EOP_N = '0' then
                             if is_last = '0' then
                                next_state <= SWAIT;
                             else
                                next_state <= SLAST;
                             end if;
                          else
                             next_state <= SLINK;
                          end if;
                       else
                          next_state <= current_state;
                       end if;
      when others =>
    end case;
  end process transitions_FA;

  -- outputs of FA
  outputs_FA: process (current_state, inner_src_rdy_n, out_dst_rdy_n, inner_eop_n,
                       inner_eof_n, RX_SRC_RDY_N, RX_EOP_N, is_last, inner_rem,
                       inner_sof_n, inner_sop_n, reg_rem, lout_rem, wout_rem, reg_first,
		        count, RX_EOF_N)
  begin
    out_rem       <= inner_rem;
    out_sof_n     <= inner_sof_n;
    out_sop_n     <= inner_sop_n;
    out_eop_n     <= inner_eop_n;
    out_eof_n     <= inner_eof_n;
    out_src_rdy_n <= inner_src_rdy_n;
    mux_ds_select <= "11";
    mux_link_select <= "11";
    next_rem <= reg_rem;
    next_first <= reg_first;
    case current_state is
            when SREAD =>
                   if inner_src_rdy_n = '0' and out_dst_rdy_n = '0' and count = PACKET_ID and inner_eop_n = '0' and inner_eof_n = '1' then
                      mux_ds_select <= "11";
                      mux_link_select <= inner_rem;
                      next_rem <= inner_rem;
		      next_first <= '1';
		      if inner_rem = "11" then
		         out_rem<="11";
                         out_eof_n <= '1';
                         out_eop_n <= '1';
		      else
                         if RX_SRC_RDY_N = '0' then
                            if RX_EOP_N = '0' then
                               if is_last = '0' then
                                  out_rem<= wout_rem;
                                  out_eop_n <= '0';
                                  if RX_EOF_N = '0' then
                                     out_eof_n <= '0';
                                  end if;
                               else
                                  out_rem<="11";
                                  out_eof_n <= '1';
                                  out_eop_n <= '1';
                               end if;
                            else
                               out_rem <= "11";
                               out_eof_n <= '1';
                               out_eop_n <= '1';
                            end if;
                         else
                            out_src_rdy_n <= '1';
                         end if;
		      end if;
                   else
		        out_src_rdy_n <= inner_src_rdy_n;
                   end if;
      when SLINK =>
                   out_sop_n <= '1';
                   if inner_src_rdy_n = '0' and out_dst_rdy_n = '0' then
                        mux_ds_select <= reg_rem;
                        mux_link_select <= reg_rem;
			next_first <= '0';
		      if reg_rem = "11" then
		         if inner_eop_n = '0' then
			    out_rem <= inner_rem;
                            out_eop_n <= '0';
		            out_src_rdy_n <= '0';
                            if inner_EOF_N = '0' then
                               out_eof_n <= '0';
                            end if;
	                 else
			    out_rem <= "11";
                            out_eof_n <= '1';
                            out_eop_n <= '1';
			    out_src_rdy_n <= '0';
		         end if;
		      else
                         if RX_SRC_RDY_N = '0' then
		            if RX_EOP_N = '0' then
                               if is_last = '0' then
                                  out_rem<= wout_rem;
                                  out_eop_n <= '0';
			          out_src_rdy_n <= '0';
                                  if RX_EOF_N = '0' then
                                     out_eof_n <= '0';
                                  end if;
                               else
                                  out_rem <= "11";
                                  out_eof_n <= '1';
                                  out_eop_n <= '1';
			          out_src_rdy_n <= '0';
                               end if;
                            else
                               out_rem <= "11";
                               out_eof_n <= '1';
                               out_eop_n <= '1';
			       out_src_rdy_n <= '0';
                            end if;
                         else
                            out_rem <= "11";
                            out_eof_n <= '1';
                            out_eop_n <= '1';
                            out_src_rdy_n <= '1';
                         end if;
		      end if;
                   else
                      out_eof_n <= '1';
                      out_eop_n <= '1';
		      out_src_rdy_n <= '1';
                   end if;
      when SLAST =>
                   mux_ds_select <= reg_rem;
                   mux_link_select <= "11";
                   if out_dst_rdy_n = '0' then
                      out_rem<= lout_rem;
                      out_eop_n <= '0';
		      out_src_rdy_n <= '0';
                      if inner_EOF_N = '0' then
                         out_eof_n <= '0';
                      end if;
                   else
                      out_eof_n <= '1';
                      out_eop_n <= '1';
		      out_src_rdy_n <= '1';
                   end if;
      when SWAIT =>
                   out_eof_n <= '1';
                   out_eop_n <= '1';
                   out_src_rdy_n <= '1';
      when SINTERNAL =>
                       if RX_SRC_RDY_N = '0' and out_dst_rdy_n = '0' then
                      if reg_first = '1' then
		        mux_ds_select <= "11";
                        mux_link_select <= reg_rem;
			next_first <= '0';
		      else
                        mux_ds_select <= reg_rem;
                        mux_link_select <= reg_rem;
		      end if;
                          if RX_EOP_N = '0' then
                             if is_last = '0' then
                                out_rem<= wout_rem;
                                out_eop_n <= '0';
				out_src_rdy_n <= '0';
                                if RX_EOF_N = '0' then
                                   out_eof_n <= '0';
                                end if;
                             else
                                out_rem<="11";
                                out_eof_n <= '1';
                                out_eop_n <= '1';
				out_src_rdy_n <= '0';
                             end if;
                          else
                              out_rem<="11";
                              out_eof_n <= '1';
                              out_eop_n <= '1';
			      out_src_rdy_n <= '0';
                          end if;
                       else
                          out_eof_n <= '1';
                          out_eop_n <= '1';
                          out_src_rdy_n <= '1';
                       end if;
      when others =>

    end case;
  end process outputs_FA;

  RX_DST_RDY_N <= inner_dst_rdy_n;
end packet_linker_arch;
