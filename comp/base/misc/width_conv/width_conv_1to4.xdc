set_multicycle_path -setup -start -from [get_pins {d*_c0_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 4
set_multicycle_path -hold         -from [get_pins {d*_c0_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 3

set_multicycle_path -setup -start -from [get_pins {d*_c1_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 3
set_multicycle_path -hold         -from [get_pins {d*_c1_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 2

set_multicycle_path -setup -start -from [get_pins {d*_c2_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 2
set_multicycle_path -hold         -from [get_pins {d*_c2_reg[*]/C}] -to [get_pins {Q*_reg[*]/D}] 1
