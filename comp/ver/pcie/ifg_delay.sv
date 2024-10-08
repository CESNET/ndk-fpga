/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

class ifg_delay;
    rand bit enabled;
    rand int unsigned length;

    //IFG => inter frame gap
    int unsigned ifg_enabled  = 1;
    int unsigned ifg_disabled = 0;
    int unsigned ifg_low      = 1;
    int unsigned ifg_high     = 18;

    constraint cDelayBase {
        enabled dist {1'b1 := ifg_enabled, 1'b0 := ifg_disabled};
        length  inside {[ifg_low:ifg_high]};
    }
endclass

