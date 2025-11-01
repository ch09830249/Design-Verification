# command line
xrun -uvm -access +r ./tb/top_tb.sv ./rtl/axi_slave_dut.sv -f ./tb/axi_flist.f

# xrun.log
* 回傳的 read data  
<img width="822" height="118" alt="image" src="https://github.com/user-attachments/assets/ae3a6864-edb4-46a7-806a-4a2de429a6c8" />

<img width="1563" height="282" alt="image" src="https://github.com/user-attachments/assets/32ca2e00-0dfa-4ee6-a226-85d69061f65d" />
<img width="883" height="482" alt="image" src="https://github.com/user-attachments/assets/9d46a477-f074-4dfd-9ee4-488a1ab0e77e" />
<img width="889" height="497" alt="image" src="https://github.com/user-attachments/assets/b1d7b0df-816d-4ce9-8f54-5d8bbcbb5388" />
<img width="893" height="488" alt="image" src="https://github.com/user-attachments/assets/56b8da0a-f532-4c53-a2d1-2d81d51ffd5a" />

```
UVM_INFO @ 0: reporter [RNTST] Running test axi_read_test...
UVM_INFO ./tb/sequence/axi_read_sequence.sv(10) @ 0: uvm_test_top.env.read_agent.sequencer@@seq [axi_read_sequence] Starting AXI read sequence
UVM_INFO ./tb/agent/axi_read_driver.sv(24) @ 0: uvm_test_top.env.read_agent.driver [axi_read_driver] before read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3659
  araddr                       integral              32    'h3e331a0e
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    0
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_driver.sv(43) @ 45000: uvm_test_top.env.read_agent.driver [axi_read_driver] after read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3659
  araddr                       integral              32    'h3e331a0e
  rdata                        integral              32    'habcd1a0e
  rresp                        integral              2     'h0
  begin_time                   time                  64    0
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 45000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Monitor read data
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3713
  araddr  integral              32    'h3e331a0e
  rdata   integral              32    'habcd1a0e
  rresp   integral              2     'h0
------------------------------------------------
UVM_INFO ./tb/agent/axi_read_driver.sv(24) @ 45000: uvm_test_top.env.read_agent.driver [axi_read_driver] before read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3698
  araddr                       integral              32    'h7b1e9aef
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    45000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 85000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Monitor read data
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3740
  araddr  integral              32    'h7b1e9aef
  rdata   integral              32    'habcd9aef
  rresp   integral              2     'h0
------------------------------------------------
UVM_INFO ./tb/agent/axi_read_driver.sv(43) @ 85000: uvm_test_top.env.read_agent.driver [axi_read_driver] after read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3698
  araddr                       integral              32    'h7b1e9aef
  rdata                        integral              32    'habcd9aef
  rresp                        integral              2     'h0
  begin_time                   time                  64    45000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_driver.sv(24) @ 85000: uvm_test_top.env.read_agent.driver [axi_read_driver] before read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3693
  araddr                       integral              32    'ha55197d1
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    85000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 125000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Monitor read data
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3720
  araddr  integral              32    'ha55197d1
  rdata   integral              32    'habcd97d1
  rresp   integral              2     'h0
------------------------------------------------
UVM_INFO ./tb/agent/axi_read_driver.sv(43) @ 125000: uvm_test_top.env.read_agent.driver [axi_read_driver] after read
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3693
  araddr                       integral              32    'ha55197d1
  rdata                        integral              32    'habcd97d1
  rresp                        integral              2     'h0
  begin_time                   time                  64    85000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/sequence/axi_read_sequence.sv(19) @ 125000: uvm_test_top.env.read_agent.sequencer@@seq [axi_read_sequence] Read transaction sent: addr=0xa55197d1
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 125000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
```
