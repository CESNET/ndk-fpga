-- reg_fifo.vhd: a primitive FIFO-like buffer from registers
-- Copyright (C) 2024 CESNET z.s.p.o.
-- Author(s): Vladislav Valek  <xvalek14@vutbr.cz>
--
-- SPDX-License-Identifier: BSD-3-Clause

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

use work.type_pack.all;
use work.math_pack.all;

-- This component is the most primitive FIFO here which is made of registers that buffers data also when the
-- output TX_DST_RDY is deasserted. In that case, the buffer keeps an output RX_DST_RDY asserted
-- unless the FIFO is full. If the TX_DST_RDY is asserted, the buffer behaves as a set of register
-- stages of the size ITEMS.
--
-- .. WARNING::
--    It is advised to use this component only on a very limited amounts of DATA_WIDTH*ITEMS.
--    Otherwise the consumption of the registers can be huge. For more items, refer to other types
--    of FIFO.
--
entity REG_FIFO is

    generic (
        -- Bit width of data
        DATA_WIDTH : natural := 256;
        ITEMS      : natural := 2;
        -- If this is true, the input data are directly connected to the output as well as the
        -- handshaking signals.
        FAKE_FIFO  : boolean := FALSE);

    port (
        CLK        : in  std_logic;
        RST        : in  std_logic;

        RX_DATA    : in  std_logic_vector(DATA_WIDTH-1 downto 0);
        RX_SRC_RDY : in  std_logic;
        RX_DST_RDY : out std_logic;

        TX_DATA    : out std_logic_vector(DATA_WIDTH -1 downto 0);
        TX_SRC_RDY : out std_logic;
        TX_DST_RDY : in  std_logic);

end entity;

architecture FULL of REG_FIFO is

    signal sb_data    : slv_array_t(ITEMS downto 0)(RX_DATA'range);
    signal sb_src_rdy : std_logic_vector(ITEMS downto 0);
    signal sb_dst_rdy : std_logic_vector(ITEMS downto 0);

begin

    fake_buff_g : if (FAKE_FIFO) generate
        TX_DATA    <= RX_DATA;
        TX_SRC_RDY <= RX_SRC_RDY;
        RX_DST_RDY <= TX_DST_RDY;
    end generate;

    not_fake_buff_g : if (not FAKE_FIFO) generate

        sb_data(0)    <= RX_DATA;
        sb_src_rdy(0) <= RX_SRC_RDY;
        RX_DST_RDY    <= sb_dst_rdy(0);

        skid_buff_stages_g : for i in 1 to ITEMS generate
            skid_buffer_p : process (CLK) is
            begin
                if (rising_edge(CLK)) then
                    if (RST = '1') then
                        sb_src_rdy(i) <= '0';
                    elsif (sb_dst_rdy(i-1) = '1') then
                        sb_data(i)    <= sb_data(i-1);
                        sb_src_rdy(i) <= sb_src_rdy(i-1);
                    end if;
                end if;
            end process;

            sb_dst_rdy(i-1) <= sb_dst_rdy(i) or (not sb_src_rdy(i));
        end generate;

        TX_DATA            <= sb_data(ITEMS);
        TX_SRC_RDY         <= sb_src_rdy(ITEMS);
        sb_dst_rdy(ITEMS) <= TX_DST_RDY;

    end generate;
end architecture;
