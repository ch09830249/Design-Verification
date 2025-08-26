# xrun.log
下方 input 和 output monitor 只會 monitor 到第一包的資訊, 原因是 driver 丟完兩包後就 drop objection, monitor 的 main phase 其實沒有 raise objection 的
```
my_env is new!!
UVM_INFO @ 0: reporter [RNTST] Running test my_env...
my_env build phase!!
UVM_INFO my_driver.sv(9) @ 0: uvm_test_top.drv [my_driver] new is called
UVM_INFO my_driver.sv(17) @ 0: uvm_test_top.drv [my_driver] build_phase is called
UVM_INFO my_driver.sv(21) @ 0: uvm_test_top.drv [my_driver] get virtual interface vif successfully!!!
UVM_INFO my_driver.sv(25) @ 0: uvm_test_top.drv [my_driver] get virtual interface vif2 successfully!!!
UVM_INFO my_monitor.sv(18) @ 0: uvm_test_top.i_mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(18) @ 0: uvm_test_top.o_mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_driver.sv(33) @ 0: uvm_test_top.drv [my_driver] main_phase is called
======================= Print Transaction (my_driver)=======================
dmac: 6232d5d7b512
smac: 43fc03080fee
ether_type: 9bf6
pload[0] = 43
pload[1] = f7
pload[2] = a5
pload[3] = ad
pload[4] = a6
pload[5] = 36
pload[6] = dc
pload[7] = 8d
pload[8] = 21
pload[9] = bf
pload[10] = 2d
pload[11] = 5d
pload[12] = 50
pload[13] = fa
pload[14] = ea
pload[15] = 94
pload[16] = fd
pload[17] = 36
pload[18] = 1b
pload[19] = 17
crc: 0
==============================================
UVM_INFO my_driver.sv(83) @ 0: uvm_test_top.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(43) @ 1300000: uvm_test_top.i_mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(43) @ 1500000: uvm_test_top.o_mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(95) @ 8700000: uvm_test_top.drv [my_driver] end drive one pkt
======================= Print Transaction (my_driver)=======================
dmac: 336bf7b5c9c8
smac: 4ff8ed9c1b3e
ether_type: b32
pload[0] = da
pload[1] = 14
pload[2] = f2
pload[3] = 38
pload[4] = fe
pload[5] = b8
pload[6] = 5e
pload[7] = 65
pload[8] = 5f
pload[9] = 1e
pload[10] = 62
pload[11] = 19
pload[12] = 84
pload[13] = 15
pload[14] = 3
pload[15] = bb
pload[16] = 36
pload[17] = 59
pload[18] = 2d
pload[19] = f0
crc: 0
==============================================
UVM_INFO my_driver.sv(83) @ 8700000: uvm_test_top.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(105) @ 8900000: uvm_test_top.i_mon [my_monitor] end collect one pkt, print it:
======================= Print Transaction (my_monitor)=======================
dmac: 12b5d7d53262
smac: ee0f0803fc43
ether_type: f69b
pload[0] = 43
pload[1] = f7
pload[2] = a5
pload[3] = ad
pload[4] = a6
pload[5] = 36
pload[6] = dc
pload[7] = 8d
pload[8] = 21
pload[9] = bf
pload[10] = 2d
pload[11] = 5d
pload[12] = 50
pload[13] = fa
pload[14] = ea
pload[15] = 94
pload[16] = fd
pload[17] = 36
pload[18] = 1b
pload[19] = 17
crc: 0
==============================================
UVM_INFO my_monitor.sv(105) @ 9100000: uvm_test_top.o_mon [my_monitor] end collect one pkt, print it:
======================= Print Transaction (my_monitor)=======================
dmac: 12b5d7d53262
smac: ee0f0803fc43
ether_type: f69b
pload[0] = 43
pload[1] = f7
pload[2] = a5
pload[3] = ad
pload[4] = a6
pload[5] = 36
pload[6] = dc
pload[7] = 8d
pload[8] = 21
pload[9] = bf
pload[10] = 2d
pload[11] = 5d
pload[12] = 50
pload[13] = fa
pload[14] = ea
pload[15] = 94
pload[16] = fd
pload[17] = 36
pload[18] = 1b
pload[19] = 17
crc: 0
==============================================
UVM_INFO my_monitor.sv(43) @ 10100000: uvm_test_top.i_mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(43) @ 10300000: uvm_test_top.o_mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(95) @ 17500000: uvm_test_top.drv [my_driver] end drive one pkt

```
