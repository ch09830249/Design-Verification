vlib work

# 編譯 DUT
vlog ./rtl/counter4.sv

# 編譯 TB
vlog +incdir+./tb ./tb/top_tb.sv

# 執行
vsim -sv_seed 1234 work.top_tb -do "log -r /*; run -all"
