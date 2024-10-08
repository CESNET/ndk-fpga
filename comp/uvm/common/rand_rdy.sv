/*
 * file       : rand_rdy.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: bound to sequencer for generating spaces
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

////////////////////////////////////////////////
// CLASS WITH BOUNDS
class rdy_bounds;
    rand int unsigned one;
    rand int unsigned zero;

    function new();
        one  = 10;
        zero = 5;
    endfunction

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        return 0;
    endfunction
endclass

class rdy_bounds_base extends rdy_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 100;

    function new();
        one = 100;
        zero = 0;
    endfunction

    constraint c_bounds {
        one  <= bound_max;
        one  >= bound_min;
        zero <= (100 - bound_min);
        zero >= (100 - bound_max);
        (zero + one) == 100;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass


class rdy_bounds_full extends rdy_bounds;
    function new();
        one = 100;
        zero = 0;
    endfunction

    constraint c_bounds {
        one  == 100;
        zero == 0;
        (zero + one) == 100;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < 100) begin
            return 0;
        end
        return 1;
    endfunction
endclass

class rdy_bounds_speed extends rdy_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 100;

    function new();
        one  = 90;
        zero = 10;
    endfunction

    constraint c_bounds {
        one  <= 100;
        one  >= 90;
        zero <= 10;
        zero >= 0;
        one  inside {[bound_min:bound_max]};
        zero inside {[(100-bound_max):(100-bound_min)]};
        (zero + one) == 100;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (max < 90) begin
            return 0;
        end
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

class rdy_bounds_mid extends rdy_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 100;

    function new();
        one  = 70;
        zero = 30;
    endfunction

    constraint c_bounds {
        one  <= 90;
        one  >= 70;
        zero <= 30;
        zero >= 10;
        one  inside {[bound_min:bound_max]};
        zero inside {[(100-bound_max):(100-bound_min)]};
        (zero + one) == 100;
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (min > 90 ||  max < 70) begin
            return 0;
        end
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

class rdy_bounds_low extends rdy_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 100;

    function new();
        one  = 50;
        zero = 50;
    endfunction

    constraint c_bounds {
        one  <= 30;
        one  >= 10;
        zero <= 70;
        zero >= 30;
        (zero + one) == 100;
        one  inside {[bound_min:bound_max]};
        zero inside {[(100-bound_max):(100-bound_min)]};
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (min > 30 || max < 10) begin
            return 0;
        end
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

class rdy_bounds_stop extends rdy_bounds;
    int unsigned bound_min = 0;
    int unsigned bound_max = 100;

    function new();
        one  = 0;
        zero = 100;
    endfunction

    constraint c_bounds {
        one  == 0;
        zero == 100;
        (zero + one) == 100;
        one  inside {[bound_min:bound_max]};
        zero inside {[(100-bound_max):(100-bound_min)]};
    };

    virtual function int unsigned bound_set(int unsigned min, int unsigned max);
        if (min > 0) begin
            return 0;
        end
        bound_min = min;
        bound_max = max;
        return 1;
    endfunction
endclass

////////////////////////////////////////////////
// RAND VALUE
class rand_rdy;
    rdy_bounds   m_bounds;
    rand logic   m_value;

    constraint c_value {
        m_value dist {1'b1 :/ m_bounds.one, 1'b0 :/ m_bounds.zero};
    };

    function new();
        m_bounds       = new();
    endfunction

    virtual function void bound_set(int unsigned min, int unsigned max);
        void'(m_bounds.bound_set(min, max));
    endfunction
endclass

// TODO: Add support for burst modes
class rand_rdy_rand extends rand_rdy;
    rdy_bounds   rand_bounds[];
    rdy_bounds   rand_bounds_active[];
    int unsigned index = 0;

    int unsigned rand_count_min = 25;
    int unsigned rand_count_max = 500;
    int unsigned rand_count;

    //only burst mode
    int unsigned ones_count;
    int unsigned zeros_count;

    typedef enum {BASE, BURST} mode_t;
    mode_t mode;

    function new(rdy_bounds bounds_arr[] = {});
        super.new();
        if (bounds_arr.size() != 0) begin
            this.rand_bounds = bounds_arr;
        end else begin
            this.rand_bounds = new[6];
            this.rand_bounds[0] = rdy_bounds_full::new();
            this.rand_bounds[1] = rdy_bounds_speed::new();
            this.rand_bounds[2] = rdy_bounds_mid::new();
            this.rand_bounds[3] = rdy_bounds_low::new();
            this.rand_bounds[4] = rdy_bounds_stop::new();
            this.rand_bounds[5] = rdy_bounds_base::new();
        end

        this.mode = BASE;
        this.rand_bounds_active = this.rand_bounds;
        this.rand_count = 0;
        this.m_bounds   = new();
    endfunction

    function void pre_randomize();
        if (rand_count == 0) begin
            rand_count = $urandom_range(rand_count_max, rand_count_min);
            index = $urandom_range(rand_bounds_active.size()-1, 0);
            void'(rand_bounds_active[index].randomize());
            //m_bounds = rand_bounds_active[index];
            void'(std::randomize(mode) with {mode dist {BASE :/ 1, BURST :/ 10};});
            ones_count  = rand_bounds_active[index].one  * real'(rand_count)/(real'(rand_bounds_active[index].one + rand_bounds_active[index].zero));
            zeros_count = rand_bounds_active[index].zero * real'(rand_count)/(real'(rand_bounds_active[index].one + rand_bounds_active[index].zero));
        end else begin
            rand_count--;
        end

        if (mode == BURST) begin
            if (ones_count != 0 || rand_bounds_active[index].one == 100) begin
               m_bounds.one  = 1;
               m_bounds.zero = 0;
               ones_count--;
            end else begin
               m_bounds.one  = 0;
               m_bounds.zero = 1;
               zeros_count--;
            end
        end else if (mode == BASE) begin
            m_bounds.one  = rand_bounds_active[index].one;
            m_bounds.zero = rand_bounds_active[index].zero;
        end
    endfunction


    // select border which can be randomized
    virtual function void bound_set(int unsigned min, int unsigned max);
        rdy_bounds selected[$];

        for (int unsigned it = 0; it < rand_bounds.size(); it++) begin
            if (rand_bounds[it].bound_set(min, max) == 1) begin
                selected.push_back(rand_bounds[it]);
            end
        end

        rand_bounds_active = selected;
    endfunction
endclass


class rand_rdy_swap extends rand_rdy;
    int unsigned ones_count;
    int unsigned zeros_count;
    int unsigned ones_active;
    int unsigned zeros_active;

    function new(int unsigned ones = 32, int unsigned zeros = 16);
        ones_count   = ones;
        zeros_count  = zeros;
        ones_active  = 0;
        zeros_active = 0;
    endfunction

    function void pre_randomize();
        if (ones_active == 0 && zeros_active == 0) begin
            zeros_active = zeros_count;
            ones_active  = ones_count;
        end

        if (ones_active != 0) begin
            ones_active--;
            m_bounds.one  = 1;
            m_bounds.zero = 0;
        end else if (zeros_active != 0) begin
            zeros_active--;
            m_bounds.one  = 0;
            m_bounds.zero = 1;
        end else begin
            m_bounds.one  = 1;
            m_bounds.zero = 1;
        end
    endfunction
endclass

