# command line
xrun -uvm -access +r ./tb/apb_write_top.sv ./rtl/apb_write_slave.sv -f ./tb/apb_write_flist.f

# xrun.log
apb_write_slave 會在 PSEL && PENABLE 之後 2 個 clk 才會舉起 PREADY, driver 則在 PREADY 舉起之後才傳送下一筆 write
<img width="1863" height="348" alt="image" src="https://github.com/user-attachments/assets/bd18d0ae-ea08-4c41-baf4-55fe6ba567ea" />

```
UVM_INFO @ 0: reporter [RNTST] Running test apb_write_test...
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 0: uvm_test_top.env.write_agent.driver [apb_write_driver] before write
------------------------------------------------------------------------------------------------------
Name                           Type                   Size  Value
------------------------------------------------------------------------------------------------------
tx                             apb_write_transaction  -     @3568
  addr                         integral               32    'he
  data                         integral               32    'hd8dfe655
  begin_time                   time                   64    0
  depth                        int                    32    'd2
  parent sequence (name)       string                 3     seq
  parent sequence (full name)  string                 42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                 38    uvm_test_top.env.write_agent.sequencer
------------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 55000: uvm_test_top.env.write_agent.driver [apb_write_driver] before write
------------------------------------------------------------------------------------------------------
Name                           Type                   Size  Value
------------------------------------------------------------------------------------------------------
tx                             apb_write_transaction  -     @3631
  addr                         integral               32    'hef
  data                         integral               32    'h36867f7a
  begin_time                   time                   64    55000
  depth                        int                    32    'd2
  parent sequence (name)       string                 3     seq
  parent sequence (full name)  string                 42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                 38    uvm_test_top.env.write_agent.sequencer
------------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 115000: uvm_test_top.env.write_agent.driver [apb_write_driver] before write
------------------------------------------------------------------------------------------------------
Name                           Type                   Size  Value
------------------------------------------------------------------------------------------------------
tx                             apb_write_transaction  -     @3630
  addr                         integral               32    'hd1
  data                         integral               32    'hfaa622eb
  begin_time                   time                   64    115000
  depth                        int                    32    'd2
  parent sequence (name)       string                 3     seq
  parent sequence (full name)  string                 42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                 38    uvm_test_top.env.write_agent.sequencer
------------------------------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 175000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```


