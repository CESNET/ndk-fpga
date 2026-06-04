-- Copyright (C) 2026 CESNET z. s. p. o.
-- Author(s): Martin Spinler <spinler@cesnet.cz>

library IEEE;
use IEEE.std_logic_1164.all;

use work.math_pack.all;
use work.type_pack.all;

package mfb is

    type cfg_mfb_t is record
        -- Input configuration
        REGIONS     : natural;
        REGION_SIZE : natural;
        BLOCK_SIZE  : natural;
        ITEM_WIDTH  : natural;
        META_WIDTH  : natural;

        -- Computed parameters
        data_w      : natural;
        sof_w       : natural;
        eof_w       : natural;
        sof_pos_w   : natural;
        eof_pos_w   : natural;
    end record;

    pure function cfg_mfb_init (REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH: natural) return cfg_mfb_t;
    pure function cfg_mfb_init (REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH: natural) return cfg_mfb_t;

end package;

package body mfb is

    pure function cfg_mfb_init (REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH: natural) return cfg_mfb_t is
        variable cfg : cfg_mfb_t;
    begin
        cfg.REGIONS     := REGIONS;
        cfg.REGION_SIZE := REGION_SIZE;
        cfg.BLOCK_SIZE  := BLOCK_SIZE;
        cfg.ITEM_WIDTH  := ITEM_WIDTH;
        cfg.META_WIDTH  := META_WIDTH;

        cfg.data_w      := REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
        cfg.sof_w       := REGIONS;
        cfg.eof_w       := REGIONS;
        cfg.sof_pos_w   := REGIONS * max(1, log2(REGION_SIZE));
        cfg.eof_pos_w   := REGIONS * max(1, log2(REGION_SIZE * BLOCK_SIZE));
        return cfg;
    end function;

    pure function cfg_mfb_init (REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH: natural) return cfg_mfb_t is
    begin
        return cfg_mfb_init(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, 0);
    end function;

end package body;
