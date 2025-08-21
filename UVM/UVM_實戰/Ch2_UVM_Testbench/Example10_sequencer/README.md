# xrun.log
```
UVM_INFO my_env.sv(16) @ 0: uvm_test_top [my_env] my_envs is new
UVM_INFO @ 0: reporter [RNTST] Running test my_env...
UVM_INFO my_env.sv(21) @ 0: uvm_test_top [my_env] my_env build phase!!
UVM_INFO my_model.sv(14) @ 0: uvm_test_top.mdl [my_model] my_model is new
UVM_INFO my_agent.sv(25) @ 0: uvm_test_top.i_agt [my_agent] my_agent is new (active)
UVM_INFO my_driver.sv(14) @ 0: uvm_test_top.i_agt.drv [my_driver] new is called
UVM_INFO my_driver.sv(22) @ 0: uvm_test_top.i_agt.drv [my_driver] build_phase is called
UVM_INFO my_driver.sv(26) @ 0: uvm_test_top.i_agt.drv [my_driver] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.i_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_model.sv(19) @ 0: uvm_test_top.mdl [my_model] main_phase is called
UVM_INFO my_agent.sv(27) @ 0: uvm_test_top.o_agt [my_agent] my_agent is new (passive)
UVM_INFO my_monitor.sv(17) @ 0: uvm_test_top.o_agt.mon [my_monitor] get virtual interface vif successfully!!!
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.o_agt.mon [my_monitor] main_phase is called
UVM_INFO my_monitor.sv(28) @ 0: uvm_test_top.i_agt.mon [my_monitor] main_phase is called
UVM_INFO my_driver.sv(69) @ 1100000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(48) @ 2500000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 2700000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(80) @ 45900000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(69) @ 45900000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(63) @ 46100000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4904
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    200   -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [195]     integral        8     'hcc
    [196]     integral        8     'hc1
    [197]     integral        8     'hca
    [198]     integral        8     'h91
    [199]     integral        8     'h9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(33) @ 46100000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4993
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    200   -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [195]     integral        8     'hcc
    [196]     integral        8     'hc1
    [197]     integral        8     'hca
    [198]     integral        8     'h91
    [199]     integral        8     'h9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 46300000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4890
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    200   -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [195]     integral        8     'hcc
    [196]     integral        8     'hc1
    [197]     integral        8     'hca
    [198]     integral        8     'h91
    [199]     integral        8     'h9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(41) @ 46300000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4890
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    200   -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [195]     integral        8     'hcc
    [196]     integral        8     'hc1
    [197]     integral        8     'hca
    [198]     integral        8     'h91
    [199]     integral        8     'h9
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 47300000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 47500000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(80) @ 90700000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_monitor.sv(63) @ 90900000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4905
  dmac        integral        48    'h42966a13b594
  smac        integral        48    'he5d170e35281
  ether_type  integral        16    'h6e3c
  pload       da(integral)    200   -
    [0]       integral        8     'h4f
    [1]       integral        8     'h15
    [2]       integral        8     'h7e
    [3]       integral        8     'h88
    [4]       integral        8     'h8d
    ...       ...             ...   ...
    [195]     integral        8     'h9a
    [196]     integral        8     'he5
    [197]     integral        8     'h58
    [198]     integral        8     'h85
    [199]     integral        8     'ha8
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(63) @ 91100000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4899
  dmac        integral        48    'h42966a13b594
  smac        integral        48    'he5d170e35281
  ether_type  integral        16    'h6e3c
  pload       da(integral)    200   -
    [0]       integral        8     'h4f
    [1]       integral        8     'h15
    [2]       integral        8     'h7e
    [3]       integral        8     'h88
    [4]       integral        8     'h8d
    ...       ...             ...   ...
    [195]     integral        8     'h9a
    [196]     integral        8     'he5
    [197]     integral        8     'h58
    [198]     integral        8     'h85
    [199]     integral        8     'ha8
  crc         integral        32    'h0
--------------------------------------------------

```
