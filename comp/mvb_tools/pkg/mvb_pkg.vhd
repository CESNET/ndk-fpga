-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

package mvb is

    type cfg_mvb_t is record
        -- Input configuration
        ITEMS       : natural;
        ITEM_WIDTH  : natural;

        -- Computed parameters
        data_w      : natural;
        vld_w       : natural;
    end record;

    pure function cfg_mvb_init (ITEMS, ITEM_WIDTH : natural) return cfg_mvb_t;
end package;

package body mvb is

    pure function cfg_mvb_init (ITEMS, ITEM_WIDTH : natural) return cfg_mvb_t is
        variable cfg : cfg_mvb_t;
    begin
        cfg.ITEMS       := ITEMS;
        cfg.ITEM_WIDTH  := ITEM_WIDTH;

        cfg.data_w      := ITEMS * ITEM_WIDTH;
        cfg.vld_w       := ITEMS;
        return cfg;
    end function;

end package body;
