set CONSTR_TEXT "create_clock -name SysClk -period 2.000 \[get_ports CLK\]\n"
# specification of input and output delay because of flu2axi contains combinatorial logic only
append CONSTR_TEXT "set_input_delay -clock SysClk 0 \[all_inputs]\n"
append CONSTR_TEXT "set_output_delay -clock SysClk 0 \[all_outputs]\n"
