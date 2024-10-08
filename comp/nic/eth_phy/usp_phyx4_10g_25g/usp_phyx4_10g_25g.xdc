set GT_CELLS [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*GEN*ETH*I*"}]
set GT_RXOUTCLK_PINS [get_pins -of_objects $GT_CELLS -filter {REF_PIN_NAME=~RXOUTCLK}]
set GT_TXOUTCLK_PINS [get_pins -of_objects $GT_CELLS -filter {REF_PIN_NAME=~TXOUTCLK}]

set GT1_CELL [get_cells -hierarchical -filter { PRIMITIVE_TYPE == ADVANCED.GT.GTYE4_CHANNEL && NAME =~ "*GEN*ETH*I*_gt_1*"}]
set GT1_RXOUTCLK_PIN [get_pins -of_objects $GT1_CELL -filter {REF_PIN_NAME=~RXOUTCLK}]
set GT1_TXOUTCLK_PIN [get_pins -of_objects $GT1_CELL -filter {REF_PIN_NAME=~TXOUTCLK}]

set rxout_clks [get_clocks -of_objects $GT_RXOUTCLK_PINS]
set txout_clks [get_clocks -of_objects $GT_TXOUTCLK_PINS]
set sys_clk [get_clocks -of_objects [get_ports -no_traverse SYSCLK]]

set rxout_clk_1 [get_clocks -of_objects $GT1_RXOUTCLK_PIN]
set txout_clk_1 [get_clocks -of_objects $GT1_TXOUTCLK_PIN]

set_max_delay -from $rxout_clks -to $txout_clks -datapath_only [get_property PERIOD $rxout_clk_1]
set_max_delay -from $txout_clks -to $rxout_clks -datapath_only [get_property PERIOD $txout_clk_1]
set_max_delay -from $rxout_clks -to $sys_clk    -datapath_only [get_property PERIOD $rxout_clk_1]
set_max_delay -from $txout_clks -to $sys_clk    -datapath_only [get_property PERIOD $txout_clk_1]
set_max_delay -from $sys_clk   -to $txout_clks  -datapath_only [get_property PERIOD $sys_clk]
set_max_delay -from $sys_clk   -to $rxout_clks  -datapath_only [get_property PERIOD $sys_clk]
