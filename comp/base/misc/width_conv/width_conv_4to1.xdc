set_multicycle_path -setup      -through [get_ports D[*]] -to [get_pins {*_resync_reg[*]/D}] 4
set_multicycle_path -hold  -end -through [get_ports D[*]] -to [get_pins {*_resync_reg[*]/D}] 3
