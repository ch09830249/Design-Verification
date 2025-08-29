# command line
xrun -uvm -access +r ./tb/apb_write_top.sv ./rtl/apb_write_slave.sv -f ./tb/apb_write_flist.f

# xrun.log
apb_write_slave 會在 PSEL && PENABLE 之後 2 個 clk 才會舉起 PREADY
<img width="1564" height="320" alt="image" src="https://github.com/user-attachments/assets/73565fb8-1e6b-49fd-86f2-8da037dc6826" />
<img width="1234" height="780" alt="image" src="https://github.com/user-attachments/assets/080de4b6-e4ce-4e29-8312-9df11903ee47" />


```
UVM_INFO @ 0: reporter [RNTST] Running test apb_write_test...
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 0: uvm_test_top.env.write_agent.driver [apb_write_driver] data is drived
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
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 45000: uvm_test_top.env.write_agent.driver [apb_write_driver] data is drived
------------------------------------------------------------------------------------------------------
Name                           Type                   Size  Value
------------------------------------------------------------------------------------------------------
tx                             apb_write_transaction  -     @3568
  addr                         integral               32    'had
  data                         integral               32    'h18692789
  begin_time                   time                   64    45000
  end_time                     time                   64    45000
  depth                        int                    32    'd2
  parent sequence (name)       string                 3     seq
  parent sequence (full name)  string                 42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                 38    uvm_test_top.env.write_agent.sequencer
------------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/apb_write_driver.sv(23) @ 85000: uvm_test_top.env.write_agent.driver [apb_write_driver] data is drived
------------------------------------------------------------------------------------------------------
Name                           Type                   Size  Value
------------------------------------------------------------------------------------------------------
tx                             apb_write_transaction  -     @3568
  addr                         integral               32    'hda
  data                         integral               32    'h9034df83
  begin_time                   time                   64    85000
  end_time                     time                   64    85000
  depth                        int                    32    'd2
  parent sequence (name)       string                 3     seq
  parent sequence (full name)  string                 42    uvm_test_top.env.write_agent.sequencer.seq
  sequencer                    string                 38    uvm_test_top.env.write_agent.sequencer
------------------------------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 125000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
