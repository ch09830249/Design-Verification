# xrun.log
```
UVM_INFO my_env.sv(19) @ 0: uvm_test_top [my_env] my_envs is new
UVM_INFO @ 0: reporter [RNTST] Running test my_env...
UVM_INFO my_env.sv(24) @ 0: uvm_test_top [my_env] my_env build phase!!
UVM_INFO my_model.sv(14) @ 0: uvm_test_top.mdl [my_model] my_model is new
UVM_INFO my_agent.sv(22) @ 0: uvm_test_top.i_agt [my_agent] my_agent is new (active)
UVM_INFO my_driver.sv(9) @ 0: uvm_test_top.i_agt.drv [my_driver] new is called
UVM_INFO my_driver.sv(17) @ 0: uvm_test_top.i_agt.drv [my_driver] build_phase is called
UVM_INFO my_driver.sv(21) @ 0: uvm_test_top.i_agt.drv [my_driver] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.i_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_model.sv(19) @ 0: uvm_test_top.mdl [my_model] main_phase is called
UVM_INFO my_agent.sv(24) @ 0: uvm_test_top.o_agt [my_agent] my_agent is new (passive)
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.o_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.o_agt.mon [my_monitor] main_phase is called
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.i_agt.mon [my_monitor] main_phase is called
UVM_INFO my_driver.sv(29) @ 0: uvm_test_top.i_agt.drv [my_driver] main_phase is called
======================= Print Transaction (my_driver)=======================
dmac: b80721505e0d
smac: f5fa15c32d2f
ether_type: 3699
pload[0] = e1
pload[1] = 28
pload[2] = dc
pload[3] = 50
pload[4] = 18
pload[5] = ec
pload[6] = 20
pload[7] = 58
pload[8] = e2
pload[9] = 3e
pload[10] = de
pload[11] = c1
pload[12] = e5
pload[13] = 42
pload[14] = 5
pload[15] = ad
pload[16] = a4
pload[17] = 74
pload[18] = eb
pload[19] = 82
crc: 0
==============================================
UVM_INFO my_driver.sv(80) @ 0: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(46) @ 1300000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(46) @ 1500000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(92) @ 8700000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
======================= Print Transaction (my_driver)=======================
dmac: 42966a13b594
smac: e5d170e35281
ether_type: 6e3c
pload[0] = 4f
pload[1] = 15
pload[2] = 7e
pload[3] = 88
pload[4] = 8d
pload[5] = f8
pload[6] = d8
pload[7] = 63
pload[8] = 12
pload[9] = f6
pload[10] = b9
pload[11] = 5c
pload[12] = bf
pload[13] = ec
pload[14] = a4
pload[15] = 5f
pload[16] = 56
pload[17] = 8f
pload[18] = 2b
pload[19] = 94
crc: 0
==============================================
UVM_INFO my_driver.sv(80) @ 8700000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(83) @ 8900000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
======================= Print Transaction (my_monitor)=======================
dmac: d5e502107b8
smac: 2f2dc315faf5
ether_type: 9936
pload[0] = e1
pload[1] = 28
pload[2] = dc
pload[3] = 50
pload[4] = 18
pload[5] = ec
pload[6] = 20
pload[7] = 58
pload[8] = e2
pload[9] = 3e
pload[10] = de
pload[11] = c1
pload[12] = e5
pload[13] = 42
pload[14] = 5
pload[15] = ad
pload[16] = a4
pload[17] = 74
pload[18] = eb
pload[19] = 82
crc: 0
==============================================
UVM_INFO my_model.sv(33) @ 8900000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
======================= Print Transaction (my_model)=======================
dmac: d5e502107b8
smac: 2f2dc315faf5
ether_type: 9936
pload[0] = e1
pload[1] = 28
pload[2] = dc
pload[3] = 50
pload[4] = 18
pload[5] = ec
pload[6] = 20
pload[7] = 58
pload[8] = e2
pload[9] = 3e
pload[10] = de
pload[11] = c1
pload[12] = e5
pload[13] = 42
pload[14] = 5
pload[15] = ad
pload[16] = a4
pload[17] = 74
pload[18] = eb
pload[19] = 82
crc: 0
==============================================
UVM_INFO my_monitor.sv(83) @ 9100000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
======================= Print Transaction (my_monitor)=======================
dmac: d5e502107b8
smac: 2f2dc315faf5
ether_type: 9936
pload[0] = e1
pload[1] = 28
pload[2] = dc
pload[3] = 50
pload[4] = 18
pload[5] = ec
pload[6] = 20
pload[7] = 58
pload[8] = e2
pload[9] = 3e
pload[10] = de
pload[11] = c1
pload[12] = e5
pload[13] = 42
pload[14] = 5
pload[15] = ad
pload[16] = a4
pload[17] = 74
pload[18] = eb
pload[19] = 82
crc: 0
==============================================
UVM_INFO my_scoreboard.sv(48) @ 9100000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY
UVM_INFO my_monitor.sv(46) @ 10100000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(46) @ 10300000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(92) @ 17500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(37) @ 17500000: uvm_test_top.i_agt.drv [my_driver] main_phase is ended
```
