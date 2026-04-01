# 建立 work lib
vlib work

# 編譯 DUT
vlog -sv +incdir+./rtl ./rtl/axi_slave_dut.sv

# 編譯 UVM VIP/PKG
vlog -sv +incdir+./common +incdir+./vip +incdir+./tb ./common/pkg.sv

# 編譯 top_tb
vlog -sv +incdir+./tb ./tb/top_tb.sv

# 執行模擬
vsim -sv_seed 1234 work.top_tb -do "log -r /*; run -all"