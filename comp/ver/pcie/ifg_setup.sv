/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * SPDX-License-Identifier: BSD-3-Clause
*/

///////////////////////////////////////////////////
// RANDOMIZATION IFG CONGIG
///////////////////////////////////////////////////
class ifg_config_setup;
    //rand count have to be set to zero
    int unsigned rand_count   = 0;
    int unsigned ifg_enabled  = 0;
    int unsigned ifg_disabled = 1;
    int unsigned ifg_low      = 0;
    int unsigned ifg_high     = 18;

    function void display(string prefix = "");
        $write("=================================================\n");
        $write("== %s\n", prefix);
        $write("=================================================\n");
        $write("\trand count   : %d\n", rand_count);
        $write("\tifg_enabled  : %d\n", ifg_enabled);
        $write("\tifg_disabled : %d\n", ifg_disabled);
        $write("\tifg_low      : %d\n", ifg_low);
        $write("\tifg_high     : %d\n", ifg_high);
    endfunction
endclass

///////////////////////////////////////////////////
// RANDOMIZATION IFG CONGIG
///////////////////////////////////////////////////
class ifg_config_setup_slow extends ifg_config_setup;
    rand int unsigned rand_rand_count;
    int unsigned rand_count_min =  100;
    int unsigned rand_count_max = 1000;

    constraint c1{
       rand_rand_count inside {[rand_count_min:rand_count_max]};
    };

    function void post_randomize();
        this.rand_count   = rand_rand_count;
        this.ifg_enabled  = 90;
        this.ifg_disabled = 10;
        this.ifg_low      = 0;
        this.ifg_high     = 60;
    endfunction
endclass

///////////////////////////////////////////////////
// RANDOMIZATION IFG CONGIG
///////////////////////////////////////////////////
class ifg_config_setup_fast extends ifg_config_setup;
    rand int unsigned rand_rand_count;
    int unsigned rand_count_min =  100;
    int unsigned rand_count_max = 1000;

    constraint c1{
       rand_rand_count inside {[rand_count_min:rand_count_max]};
    };

    function void post_randomize();
        this.rand_count   = rand_rand_count;
        this.ifg_enabled  = 0;
        this.ifg_disabled = 90;
        this.ifg_low      = 0;
        this.ifg_high     = 0;
    endfunction
endclass

///////////////////////////////////////////////////
// RANDOMIZATION IFG CONGIG
///////////////////////////////////////////////////
class ifg_config_setup_rand extends ifg_config_setup;
    //rand count have to be set to zero
    rand int unsigned rand_rand_count   = 0;
    rand int unsigned rand_ifg_enabled  = 0;
    rand int unsigned rand_ifg_disabled = 1;
    rand int unsigned rand_ifg_low      = 0;
    rand int unsigned rand_ifg_high     = 18;

    //setup variables
    int unsigned ifg_enabled_min  = 0;
    int unsigned ifg_enabled_max  = 30;
    int unsigned ifg_disabled_min = 10;
    int unsigned ifg_disabled_max = 100;
    int unsigned ifg_low_min      = 0;
    int unsigned ifg_low_max      = 10;
    int unsigned ifg_high_min     = 5;
    int unsigned ifg_high_max     = 30;

    int unsigned rand_count_min = 100;
    int unsigned rand_count_max = 1000;

    constraint c1{
       rand_rand_count inside {[rand_count_min:rand_count_max]};
       //delay enabled
       rand_ifg_enabled   inside {[ifg_enabled_min:ifg_enabled_max]};
       rand_ifg_disabled  inside {[ifg_disabled_min:ifg_disabled_max]};
       (rand_ifg_enabled != 0) || (rand_ifg_disabled != 0);
       //delay long
       rand_ifg_low <= rand_ifg_high;
       rand_ifg_low  inside {[ifg_low_min:ifg_low_max]};
       rand_ifg_high inside {[ifg_high_min:ifg_high_max]};
    };

    function void post_randomize();
        this.rand_count    = rand_rand_count;
        this.ifg_enabled   = rand_ifg_enabled;
        this.ifg_disabled  = rand_ifg_disabled;
        this.ifg_low       = rand_ifg_low;
        this.ifg_high      = rand_ifg_high;
    endfunction
endclass

//rand medium
class ifg_config_setup_rand_medium extends ifg_config_setup_rand;
    function new();
        this.ifg_enabled_min  = 30;
        this.ifg_enabled_max  = 50;
        this.ifg_disabled_min = 30;
        this.ifg_disabled_max = 70;
        this.ifg_low_min      = 0;
        this.ifg_low_max      = 20;
        this.ifg_high_min     = 10;
        this.ifg_high_max     = 50;
    endfunction
endclass

//rand slow
class ifg_config_setup_rand_slow extends ifg_config_setup_rand;
    function new();
        this.ifg_enabled_min  = 80;
        this.ifg_enabled_max  = 100;
        this.ifg_disabled_min = 0;
        this.ifg_disabled_max = 20;
        this.ifg_low_min      = 0;
        this.ifg_low_max      = 30;
        this.ifg_high_min     = 20;
        this.ifg_high_max     = 50;
    endfunction
endclass

//rand fast
class ifg_config_setup_rand_fast extends ifg_config_setup_rand;
    function new();
        this.ifg_enabled_min  = 0;
        this.ifg_enabled_max  = 30;
        this.ifg_disabled_min = 60;
        this.ifg_disabled_max = 90;
        this.ifg_low_min      = 0;
        this.ifg_low_max      = 20;
        this.ifg_high_min     = 10;
        this.ifg_high_max     = 40;
    endfunction
endclass

//rand long spaces
class ifg_config_setup_rand_long_spaces extends ifg_config_setup_rand;
    function new();
        this.ifg_enabled_min  = 0;
        this.ifg_enabled_max  = 10;
        this.ifg_disabled_min = 90;
        this.ifg_disabled_max = 100;
        this.ifg_low_min      = 30;
        this.ifg_low_max      = 100;
        this.ifg_high_min     = 60;
        this.ifg_high_max     = 300;
    endfunction
endclass

///////////////////////////////////////////////////
// RANDOMIZATION IFG LIB
///////////////////////////////////////////////////
// library randomly pick some of sequence and run them
class ifg_config_setup_lib extends ifg_config_setup;
    typedef enum {IFG_SLOW, IFG_FAST, IFG_RAND_MEDIUM, IFG_RAND_SLOW, IFG_RAND_FAST, IFG_RAND_LONG_SPACES} ifg_config_type;

    rand ifg_config_type ifg_type;
    ifg_config_setup ifg[ifg_config_type];

    //distribution parameters

    int unsigned dist_slow = 7;
    int unsigned dist_fast = 7;
    int unsigned dist_rand_medium = 50;
    int unsigned dist_rand_slow   = 10;
    int unsigned dist_rand_fast   = 25;
    int unsigned dist_rand_long_spaces = 1;

    function new();
        ifg[IFG_SLOW]  = ifg_config_setup_slow::new();
        ifg[IFG_FAST]  = ifg_config_setup_fast::new();
        ifg[IFG_RAND_MEDIUM] = ifg_config_setup_rand_medium::new();
        ifg[IFG_RAND_SLOW]   = ifg_config_setup_rand_slow::new();
        ifg[IFG_RAND_FAST]   = ifg_config_setup_rand_fast::new();
        ifg[IFG_RAND_LONG_SPACES] = ifg_config_setup_rand_long_spaces::new();
    endfunction

    constraint c1{
        ifg_type dist {IFG_SLOW :/ dist_slow,  IFG_FAST :/ dist_fast, IFG_RAND_MEDIUM :/ dist_rand_medium,
                       IFG_RAND_SLOW :/ dist_rand_slow, IFG_RAND_FAST :/ dist_rand_fast, IFG_RAND_LONG_SPACES :/ dist_rand_long_spaces};
    };

    function void post_randomize();
        assert(ifg[ifg_type].randomize());
        this.rand_count   = ifg[ifg_type].rand_count;
        this.ifg_enabled  = ifg[ifg_type].ifg_enabled;
        this.ifg_disabled = ifg[ifg_type].ifg_disabled;
        this.ifg_low      = ifg[ifg_type].ifg_low;
        this.ifg_high     = ifg[ifg_type].ifg_high;
    endfunction
endclass
