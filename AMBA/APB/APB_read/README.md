# command line
xrun -uvm -access +r ./tb/apb_read_top.sv ./rtl/apb_read_slave.sv -f ./tb/apb_read_flist.f
# xrun.log
<img width="1871" height="362" alt="image" src="https://github.com/user-attachments/assets/fbf2eff5-8640-4fb9-884b-6ccb9d6806b3" />

可以看到 before read 的 addr 和 after read 的 data 是如預期的
<img width="653" height="76" alt="image" src="https://github.com/user-attachments/assets/acbf00d9-4f33-4dec-94c2-e2dbc9584e56" />

<img width="945" height="394" alt="image" src="https://github.com/user-attachments/assets/4c773eca-b43e-446c-80d6-267699793a74" />
<img width="946" height="395" alt="image" src="https://github.com/user-attachments/assets/6a486fc8-bcba-4605-89ca-6e9d952aed7c" />
<img width="948" height="397" alt="image" src="https://github.com/user-attachments/assets/9e780df4-4d6f-4cdf-a874-408b18dc3174" />
<img width="952" height="397" alt="image" src="https://github.com/user-attachments/assets/be71452b-4dc2-422b-bb38-4a38f1a5e634" />

```
UVM_INFO @ 0: reporter [RNTST] Running test apb_read_test...
UVM_INFO ./tb/agent/apb_read_driver.sv(21) @ 0: uvm_test_top.env.write_agent.driver [apb_read_driver] before read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3568
  addr                         integral              32    'h1000
  data                         integral              32    'h0
  begin_time                   time                  64    0
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(46) @ 35000: uvm_test_top.env.write_agent.driver [apb_read_driver] after read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3568
  addr                         integral              32    'h1000
  data                         integral              32    'ha5a50000
  begin_time                   time                  64    0
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(21) @ 35000: uvm_test_top.env.write_agent.driver [apb_read_driver] before read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3638
  addr                         integral              32    'h1004
  data                         integral              32    'h0
  begin_time                   time                  64    35000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(46) @ 75000: uvm_test_top.env.write_agent.driver [apb_read_driver] after read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3638
  addr                         integral              32    'h1004
  data                         integral              32    'ha5a50001
  begin_time                   time                  64    35000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(21) @ 75000: uvm_test_top.env.write_agent.driver [apb_read_driver] before read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3639
  addr                         integral              32    'h1008
  data                         integral              32    'h0
  begin_time                   time                  64    75000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(46) @ 115000: uvm_test_top.env.write_agent.driver [apb_read_driver] after read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3639
  addr                         integral              32    'h1008
  data                         integral              32    'ha5a50002
  begin_time                   time                  64    75000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(21) @ 115000: uvm_test_top.env.write_agent.driver [apb_read_driver] before read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3579
  addr                         integral              32    'h100c
  data                         integral              32    'h0
  begin_time                   time                  64    115000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_read_driver.sv(46) @ 155000: uvm_test_top.env.write_agent.driver [apb_read_driver] after read
-----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
-----------------------------------------------------------------------------------------------------
tx                             apb_read_transaction  -     @3579
  addr                         integral              32    'h100c
  data                         integral              32    'ha5a50003
  begin_time                   time                  64    115000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                38    uvm_test_top.env.write_agent.sequencer
-----------------------------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 155000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```

