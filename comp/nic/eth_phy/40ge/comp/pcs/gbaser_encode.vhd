-- gbaser_encode.vhd : 40/100GBASE-R (64/66) multi-lane encoder
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.gbaser_types.all;

entity gbaser_encode is
    generic (
        LANES : natural := 4
    );
    port (
        RESET   : in std_logic; -- Sync reset - set the FSM into initial state
        CLK     : in std_logic; -- TX clock, 322 MHz
        -- RS/MAC interface -------------------------
        D       : in  std_logic_vector(LANES*64-1 downto 0); -- TX MII data
        C       : in  std_logic_vector(LANES* 8-1 downto 0); -- TX MII command
        -- PMA interface --------------------------
        TXD     : out std_logic_vector(LANES*66-1 downto 0) -- GBASE-R encoded block payload
    );
end gbaser_encode;

-- ----------------------------------------------------------------------------
--             Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of gbaser_encode is

type tx_state_t is (IDLE, START, DATA, TERM, ERROR);
type tx_state_arr_t is array (LANES-1 downto 0) of tx_state_t;

signal state_r     : tx_state_t;
signal curr_state  : tx_state_arr_t;

begin

encoders_gen: for i in 0 to LANES-1 generate
    signal blk_type   : std_logic_vector(3-1 downto 0);
    signal blk_data   : std_logic_vector(66-1 downto 0);
    signal prev_state : tx_state_t;
begin

    encode_i: entity work.blk_enc
    port map (
        -- RS/MAC interface -------------------------
        D        => D(i*64+63 downto i*64),
        C        => C(i*8+7   downto i* 8),
        -- PMA interface --------------------------
        TXD      => blk_data,
        -- Control
        BLK_TYPE => blk_type,
        TXLF     => '0'
    );

    prev_state_0_g: if i = 0 generate
         prev_state <= state_r;
    end generate;
    prev_state_g: if i > 0 generate
        prev_state <= curr_state(i-1);
    end generate;

    curr_state(i) <=
        IDLE  when ((blk_type = C_BLKT_CTRL)  and (prev_state = IDLE  or prev_state = TERM or prev_state = ERROR))  else
        START when ((blk_type = C_BLKT_START) and (prev_state = IDLE  or prev_state = TERM))                        else
        DATA  when ((blk_type = C_BLKT_DATA)  and (prev_state = START or prev_state = DATA or prev_state = ERROR))  else
        TERM  when ((blk_type = C_BLKT_TERM)  and (prev_state = DATA  or prev_state = ERROR))                       else
        ERROR;

    txd_out_r: process(CLK)
    begin
        if rising_edge(CLK) then
            if curr_state(i) = ERROR then
                TXD(i*66+65 downto i*66) <= C_BLK_ERR;
            else
                TXD(i*66+65 downto i*66) <= blk_data;
            end if;
        end if;
    end process;

end generate;

state_r_p: process(CLK)
begin
    if rising_edge(CLK) then
        if reset = '1' then
            state_r <= IDLE;
        else
            state_r <= curr_state(LANES-1);
        end if;
    end if;
end process;

end behavioral;
