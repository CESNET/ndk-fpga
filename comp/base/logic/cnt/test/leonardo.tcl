clean_all

set period 6.4
set register2register $period
set input2register    $period
set output2register   $period
# --------------------------------------------------------------------------
# technology library setting
set part 2V1000fg456
set process 4
set wire_table xcv2-1000-4_wc
load_library xcv2

# --------------------------------------------------------------------------
# read input files
analyze ../cnt_types.vhd
analyze ../cnt.vhd
analyze top_level.vhd

elaborate fpga

# --------------------------------------------------------------------------
# pre-optimize
pre_optimize -common_logic -unused_logic -boundary -xor_comparator_optimize \
-extract

optimize -chip -target xcv2 -hierarchy flatten -effort standard -delay

set_xilinx_eqn
eval "write -format edif top_level.edf"

