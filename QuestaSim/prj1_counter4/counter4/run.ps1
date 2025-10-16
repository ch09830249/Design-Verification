$seed = Get-Date -Format "HHmmssff"

vlib work

# 編譯 DUT
vlog ./rtl/counter4.sv

# 編譯 TB
vlog +incdir+./tb ./tb/tb_top.sv

# 執行
vsim -sv_seed $seed work.tb_top -do "log -r /*; run -all"