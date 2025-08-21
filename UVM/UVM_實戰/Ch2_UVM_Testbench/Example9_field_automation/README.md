# xrun.log
1. Drive transaction
<img width="713" height="351" alt="image" src="https://github.com/user-attachments/assets/a14dc720-3402-45a7-aed7-2cd04e846970" />

2. Input monitor
<img width="851" height="333" alt="image" src="https://github.com/user-attachments/assets/1e2d7a89-c3a2-49b8-a1b3-823eb9c3e5e7" />

3. Reference model receives transaction
<img width="826" height="333" alt="image" src="https://github.com/user-attachments/assets/7f6adc66-8449-47f6-bec4-b1500ad5a450" />

4. Scoreboard compares transaction
<img width="874" height="336" alt="image" src="https://github.com/user-attachments/assets/5ab58dda-dc02-4cc0-8216-21aea48a88c8" />


```
UVM_INFO my_env.sv(16) @ 0: uvm_test_top [my_env] my_envs is new
UVM_INFO @ 0: reporter [RNTST] Running test my_env...
UVM_INFO my_env.sv(21) @ 0: uvm_test_top [my_env] my_env build phase!!
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
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4254
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    20    -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [15]      integral        8     'had
    [16]      integral        8     'ha4
    [17]      integral        8     'h74
    [18]      integral        8     'heb
    [19]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_driver.sv(99) @ 0: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(48) @ 1300000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 1500000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(118) @ 8700000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @5
  dmac        integral        48    'h42966a13b594
  smac        integral        48    'he5d170e35281
  ether_type  integral        16    'h6e3c
  pload       da(integral)    20    -
    [0]       integral        8     'h4f
    [1]       integral        8     'h15
    [2]       integral        8     'h7e
    [3]       integral        8     'h88
    [4]       integral        8     'h8d
    ...       ...             ...   ...
    [15]      integral        8     'h5f
    [16]      integral        8     'h56
    [17]      integral        8     'h8f
    [18]      integral        8     'h2b
    [19]      integral        8     'h94
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_driver.sv(99) @ 8700000: uvm_test_top.i_agt.drv [my_driver] begin to drive one pkt
UVM_INFO my_monitor.sv(104) @ 8900000: uvm_test_top.i_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4245
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    20    -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [15]      integral        8     'had
    [16]      integral        8     'ha4
    [17]      integral        8     'h74
    [18]      integral        8     'heb
    [19]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_model.sv(36) @ 8900000: uvm_test_top.mdl [my_model] get one transaction, copy and print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
new_tr        my_transaction  -     @4304
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    20    -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [15]      integral        8     'had
    [16]      integral        8     'ha4
    [17]      integral        8     'h74
    [18]      integral        8     'heb
    [19]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(104) @ 9100000: uvm_test_top.o_agt.mon [my_monitor] end collect one pkt, print it:
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4230
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    20    -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [15]      integral        8     'had
    [16]      integral        8     'ha4
    [17]      integral        8     'h74
    [18]      integral        8     'heb
    [19]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_scoreboard.sv(42) @ 9100000: uvm_test_top.scb [my_scoreboard] Compare SUCCESSFULLY and print it!
--------------------------------------------------
Name          Type            Size  Value
--------------------------------------------------
tr            my_transaction  -     @4230
  dmac        integral        48    'hb80721505e0d
  smac        integral        48    'hf5fa15c32d2f
  ether_type  integral        16    'h3699
  pload       da(integral)    20    -
    [0]       integral        8     'he1
    [1]       integral        8     'h28
    [2]       integral        8     'hdc
    [3]       integral        8     'h50
    [4]       integral        8     'h18
    ...       ...             ...   ...
    [15]      integral        8     'had
    [16]      integral        8     'ha4
    [17]      integral        8     'h74
    [18]      integral        8     'heb
    [19]      integral        8     'h82
  crc         integral        32    'h0
--------------------------------------------------
UVM_INFO my_monitor.sv(48) @ 10100000: uvm_test_top.i_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_monitor.sv(48) @ 10300000: uvm_test_top.o_agt.mon [my_monitor] begin to collect one pkt
UVM_INFO my_driver.sv(118) @ 17500000: uvm_test_top.i_agt.drv [my_driver] end drive one pkt
UVM_INFO my_driver.sv(38) @ 17500000: uvm_test_top.i_agt.drv [my_driver] main_phase is ended
```
