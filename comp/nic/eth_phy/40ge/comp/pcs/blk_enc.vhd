-- blk_enc.vhd : 40/100GBASE-R block (64/66) single lane encoder
-- Copyright (C) 2023 CESNET z. s. p. o.
-- Author(s): Stepan Friedl <friedl@cesnet.cz>
--

library ieee;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;
use work.gbaser_types.all;

entity blk_enc is
    port (
        D       : in  std_logic_vector(63 downto 0); -- TX MII data
        C       : in  std_logic_vector( 7 downto 0); -- TX MII command
        -- PMA interface --------------------------
        TXD     : out std_logic_vector(65 downto 0); -- GBASE-R encoded block payload
        -- Control
        BLK_TYPE   : out std_logic_vector(2 downto 0);
        TXLF       : in  std_logic
    );
end blk_enc;

-- ----------------------------------------------------------------------------
--             Architecture declaration
-- ----------------------------------------------------------------------------
architecture behavioral of blk_enc is

signal mii_idle      : std_logic_vector( 7 downto 0);
signal mii_term      : std_logic_vector( 7 downto 0);
signal mii_err       : std_logic_vector( 7 downto 0);

signal blk_start     : std_logic_vector(65 downto 0);
signal blk_seq       : std_logic_vector(65 downto 0);
signal blk_term_1    : std_logic_vector(65 downto 0);
signal blk_term_2    : std_logic_vector(65 downto 0);
signal blk_term_3    : std_logic_vector(65 downto 0);
signal blk_term_4    : std_logic_vector(65 downto 0);
signal blk_term_5    : std_logic_vector(65 downto 0);
signal blk_term_6    : std_logic_vector(65 downto 0);
signal blk_term_7    : std_logic_vector(65 downto 0);

begin

blk_start  <= D(63 downto 8)                                                                  & BT_S_D  & C_HDR;
blk_seq    <= X"0000000"                                          & O_C      & D(31 downto 8) & BT_O_C  & C_HDR;
blk_term_1 <= IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & "000000" & D(7 downto 0) & BT_D1_C & C_HDR;
blk_term_2 <= IDLE_C & IDLE_C & IDLE_C & IDLE_C & IDLE_C & "00000"           & D(15 downto 0) & BT_D2_C & C_HDR;
blk_term_3 <= IDLE_C & IDLE_C & IDLE_C & IDLE_C & "0000"                     & D(23 downto 0) & BT_D3_C & C_HDR;
blk_term_4 <= IDLE_C & IDLE_C & IDLE_C & "000"                               & D(31 downto 0) & BT_D4_C & C_HDR;
blk_term_5 <= IDLE_C & IDLE_C & "00"                                         & D(39 downto 0) & BT_D5_C & C_HDR;
blk_term_6 <= IDLE_C & "0"                                                   & D(47 downto 0) & BT_D6_C & C_HDR;
blk_term_7 <=                                                                  D(55 downto 0) & BT_D7_T & C_HDR;

mii_codes_g: for i in 0 to 7 generate
    mii_idle(i) <= '1' when D(8*i + 7 downto 8*i) = X"07" else '0';
    mii_term(i) <= '1' when D(8*i + 7 downto 8*i) = X"FD" else '0';
    mii_err(i)  <= not mii_idle(i);
end generate;

encode_p: process(all)
begin
    case C is
        when X"00" => -- Control - all data
            TXD      <= D & D_HDR;
            BLK_TYPE <= C_BLKT_DATA;

        when X"FF" => -- all control characters
            if mii_term(0) = '1' then -- Terminate, no data
                TXD      <= C_BLK_TERM0;   -- TERM type
                BLK_TYPE <= C_BLKT_TERM;
            elsif (mii_err /= "00000000") then
                TXD      <= C_BLK_ERR;     -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            else -- Idle
                TXD      <= C_BLK_IDLE;   -- IDLE type
                BLK_TYPE <= C_BLKT_CTRL;
            end if;

        -- Start or sequence
        when X"01" =>
            if D(7 downto 0) = X"FB" then -- Start + 7 data
                TXD      <= blk_start;   -- TERM type
                BLK_TYPE <= C_BLKT_START;
            elsif D(7 downto 0) = X"9C" then -- Sequence
                TXD      <= blk_seq;
                BLK_TYPE <= C_BLKT_CTRL;
            else
                TXD      <= C_BLK_ERR;   -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        -- Terminate with 1 data
        when X"FE" =>
            if mii_term(1) = '1' then
                if mii_idle(7 downto 2) = "111111" then
                    TXD      <= blk_term_1;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        -- Terminate with 2 data
        when X"FC" =>
            if mii_term(2) = '1' then
                if mii_idle(7 downto 3) = "11111" then
                    TXD      <= blk_term_2;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when X"F8" => -- Terminate with 3 data
            if mii_term(3) = '1' then
                if mii_idle(7 downto 4) = "1111" then
                    TXD      <= blk_term_3;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when X"F0" => -- Terminate with 4 data
            if mii_term(4) = '1' then
                if mii_idle(7 downto 5) = "111" then
                    TXD      <= blk_term_4;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when X"E0" => -- Terminate with 5 data
            if mii_term(5) = '1' then
                if mii_idle(7 downto 6) = "11" then
                    TXD      <= blk_term_5;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when X"C0" => -- Terminate with 6 data
            if mii_term(6) = '1' then
                if mii_idle(7 downto 7) = "1" then
                    TXD      <= blk_term_6;
                    BLK_TYPE <= C_BLKT_TERM;
                else
                    TXD      <= C_BLK_ERR;  -- ERR type
                    BLK_TYPE <= C_BLKT_ERR;
                end if;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when X"80" => -- Terminate with 7 data
            if mii_term(7) = '1' then
                TXD      <= blk_term_7;
                BLK_TYPE <= C_BLKT_TERM;
            else
                TXD      <= C_BLK_ERR;      -- ERR type
                BLK_TYPE <= C_BLKT_ERR;
            end if;

        when others =>
            TXD      <= C_BLK_ERR;     -- ERR type
            BLK_TYPE <= C_BLKT_ERR;
    end case;

end process;
--

end behavioral;
