/*
 * file       : rand_length.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: length randomization
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

////////////////////////////////////////////////
// CLASS WITH BOUNDS
class length_bounds;
    rand int unsigned min;
    rand int unsigned max;

    constraint c_main {
        min <= max;
    };

    function new();
        min = 5;
        max = 10;
    endfunction

    //this function set minimal and maximal generated value
    //return 1 if bound min and max can be suttisfied
    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        return 0;
    endfunction
endclass

////////////////////////////////////////////////
// This class generates number from min to max
class length_bounds_base extends length_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 1000;

    constraint c_main {
        min inside {[bound_min:bound_max]};
        max inside {[bound_min:bound_max]};
        min <= max;
    };

    function new();
        min = 0;
        max = 0;
    endfunction

    constraint c_bounds {
        min >= bound_min + 0;
        min <= bound_max + 0;
        max >= bound_min + 0;
        max <= bound_max + 0;
    };

    //return 1 if bound min and max can be suttisfied
    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

////////////////////////////////////////////////
// This class generates smallest number
class length_bounds_min extends length_bounds;
    int unsigned bound_min = 0;

    function new();
        min = 0;
        max = 0;
    endfunction

    constraint c_bounds {
        min >= bound_min + 0;
        min <= bound_min + 0;
        max >= bound_min + 0;
        max <= bound_min + 0;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        bound_min = min;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generates small  number
class length_bounds_smaller extends length_bounds;
    int unsigned bound_min = 0;

    function new();
        min = 0;
        max = 15;
    endfunction

    constraint c_bounds {
        min >= bound_min + 0;
        min <= bound_min + 15;
        max >= bound_min + 0;
        max <= bound_min + 15;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < (min + 15)) begin
            return 0;
        end
        bound_min = min;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generates small  number
class length_bounds_small extends length_bounds;
    int unsigned bound_min = 0;

    function new();
        min = 15;
        max = 30;
    endfunction

    constraint c_bounds {
        min >= bound_min + 15;
        min <= bound_min + 30;
        max >= bound_min + 15;
        max <= bound_min + 30;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < (min < 30)) begin
            return 0;
        end
        bound_min = min;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generates number in middle of bounds
class length_bounds_mid extends length_bounds;
    int unsigned middle = 750;

    function new();
        min = 15;
        max = 30;
    endfunction

    constraint c_bounds {
        min >= middle - 250;
        min <= middle + 250;
        max >= middle - 250;
        max <= middle + 250;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < (min + 500)) begin
            return 0;
        end
        middle = min + (max - min)/2;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generates number near end of bounds
class length_bounds_long extends length_bounds;
    int unsigned bound_max = 1300;

    function new();
        min = 1600;
        max = 1600;
    endfunction

    constraint c_bounds {
        min >= bound_max - 300;
        min <= bound_max;
        max >= bound_max - 300;
        max <= bound_max;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < (min + 300)) begin
            return 0;
        end
        bound_max = max;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generate maximum number
class length_bounds_max extends length_bounds;
    int unsigned bound_max = 1600;

    function new();
        min = 1600;
        max = 1600;
    endfunction

    constraint c_bounds {
        min == bound_max;
        max == bound_max;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        bound_max = max;
        return 1;
    endfunction
endclass

///////////////////////////////////////////////
// This class generate constant number
class length_bounds_size extends length_bounds;
    int unsigned bound_min;
    int unsigned bound_max;
    int unsigned size;

    function new();
        min = 0;
        max = 0;
    endfunction

    constraint c_bounds {
        min == size;
        max == size;
    };

    function void pre_randomize();
       size = $urandom_range(bound_max, bound_min);
    endfunction

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

////////////////////////////////////////////////
// RAND VALUE
class rand_length;
    length_bounds     m_bounds;
    rand int unsigned m_value;

    constraint c_value {
        m_value inside {[m_bounds.min:m_bounds.max]};
    };

    function new();
        m_bounds = length_bounds_base::new();
    endfunction

    virtual function void bound_set(int unsigned min, int unsigned max);
        void'(m_bounds.bound_set(min, max));
    endfunction
endclass

////////////////////////////////////////////////
// RAND VALUE
class rand_length_rand extends rand_length;
    length_bounds rand_bounds[];
    length_bounds rand_bounds_active[];
    int unsigned  rand_count_min = 25;
    int unsigned  rand_count_max = 500;
    int unsigned  rand_count;

    function new(length_bounds bounds_arr[] = {});
        super.new();
        if (bounds_arr.size() != 0) begin
            this.rand_bounds = bounds_arr;
        end else begin
            length_bounds m_new;
            length_bounds stack[$];

            m_new = length_bounds_base::new();
            stack.push_back(m_new);
            m_new = length_bounds_min::new();
            stack.push_back(m_new);
            m_new = length_bounds_smaller::new();
            stack.push_back(m_new);
            m_new = length_bounds_small::new();
            stack.push_back(m_new);
            m_new = length_bounds_mid::new();
            stack.push_back(m_new);
            m_new = length_bounds_long::new();
            stack.push_back(m_new);
            m_new = length_bounds_max::new();
            stack.push_back(m_new);
            m_new = length_bounds_size::new();
            stack.push_back(m_new);

            this.rand_bounds = stack;
        end

        this.rand_bounds_active = this.rand_bounds;
        rand_count = 0;
    endfunction

    function void pre_randomize();
        if (rand_count == 0) begin
            int unsigned index;
            rand_count = $urandom_range(rand_count_max, rand_count_min);
            index      = $urandom_range(rand_bounds_active.size()-1, 0);
            void'(rand_bounds_active[index].randomize());
            m_bounds = rand_bounds_active[index];
        end else begin
            rand_count--;
        end
    endfunction

    // select border which can be randomized
    virtual function void bound_set(int unsigned min, int unsigned max);
        length_bounds selected[$];

        for (int unsigned it = 0; it < rand_bounds.size(); it++) begin
            if (rand_bounds[it].bound_set(min, max) == 1) begin
                selected.push_back(rand_bounds[it]);
            end
        end

        rand_bounds_active = selected;
    endfunction
endclass

class rand_length_stable extends rand_length;
    int unsigned  rand_count_min = 25;
    int unsigned  rand_count_max = 500;
    int unsigned  rand_count;

    function new();
        super.new();
        rand_count = 0;
    endfunction

    function void pre_randomize();
        if (rand_count == 0) begin
            int unsigned  rand_size;
            rand_count = $urandom_range(rand_count_max, rand_count_min);
            assert(m_bounds.randomize());
        end else begin
            rand_count--;
        end
    endfunction
endclass


