/*
 * file       :  stats.sv
 * Copyright (C) 2021 CESNET z. s. p. o.
 * description: this class count statistics
 * date       : 2021
 * author     : Radek Iša <isa@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
*/

class stats;

    local real min;
    local real max;
    local real sum;
    local real sum2;

    int unsigned values;

    function new();
        reset();
    endfunction


    function void count(output real min, real max, real avg, real std_dev);
        real avg_local;

        min = this.min;
        max = this.max;

        // When values are not bigger than one, then the average doesn't make any sense.
        if (values > 1) begin
            avg_local = sum/values;
            avg = avg_local;

            std_dev = (1.0/(values-1)*(sum2 - values*(avg_local**2)))**0.5;
        end else begin
            // when values are one then the average is value
            // or when values are zero then the averagie make no sense
            avg = sum;
            std_dev = 0;
        end
    endfunction

    function void reset();
        values = 0;
        sum  = 0;
        sum2 = 0;
    endfunction

    function void next_val(real val);
        if (values == 0) begin
            min = val;
            max = val;
        end else begin
            if (min > val) begin
                min = val;
            end

            if (max < val) begin
               max = val;
            end
        end

        sum   += val;
        sum2  += val**2;

        values++;
    endfunction
endclass


