# command line
xrun -uvm -access +r ./tb/axi_read_top.sv ./rtl/axi_read_slave.sv -f ./tb/axi_read_flist.f

# xrun.log
* 回傳的 read data  
<img width="822" height="118" alt="image" src="https://github.com/user-attachments/assets/ae3a6864-edb4-46a7-806a-4a2de429a6c8" />

<img width="1566" height="329" alt="image" src="https://github.com/user-attachments/assets/f0a702c5-a5f6-4d98-ad10-cdec6d766ca8" />
<img width="1223" height="424" alt="image" src="https://github.com/user-attachments/assets/e761f0b5-5c7e-47d4-b58d-c3e56886d213" />
<img width="1230" height="417" alt="image" src="https://github.com/user-attachments/assets/283ec06f-6299-411c-903a-82b241137891" />
<img width="1232" height="419" alt="image" src="https://github.com/user-attachments/assets/49895169-b291-4d25-8bd0-d88f963cdfed" />


```
UVM_INFO @ 0: reporter [RNTST] Running test axi_read_test...
UVM_INFO ./tb/sequence/axi_read_sequence.sv(10) @ 0: uvm_test_top.env.read_agent.sequencer@@seq [axi_read_sequence] Starting AXI read sequence
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3659
  araddr                       integral              32    'hb74cfab1
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    0
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 55000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Read data get
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3722
  araddr  integral              32    'hb74cfab1
  rdata   integral              32    'habcdfab1
  rresp   integral              2     'h0
------------------------------------------------
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3707
  araddr                       integral              32    'hf9eeedf
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    65000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 105000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Read data get
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3659
  araddr  integral              32    'hf9eeedf
  rdata   integral              32    'habcdeedf
  rresp   integral              2     'h0
------------------------------------------------
----------------------------------------------------------------------------------------------------
Name                           Type                  Size  Value
----------------------------------------------------------------------------------------------------
tr                             axi_read_transaction  -     @3736
  araddr                       integral              32    'hc042d739
  rdata                        integral              32    'h0
  rresp                        integral              2     'h0
  begin_time                   time                  64    115000
  depth                        int                   32    'd2
  parent sequence (name)       string                3     seq
  parent sequence (full name)  string                41    uvm_test_top.env.read_agent.sequencer.seq
  sequencer                    string                37    uvm_test_top.env.read_agent.sequencer
----------------------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/axi_read_monitor.sv(34) @ 155000: uvm_test_top.env.read_agent.monitor [axi_read_monitor] Read data get
------------------------------------------------
Name      Type                  Size  Value
------------------------------------------------
tr        axi_read_transaction  -     @3707
  araddr  integral              32    'hc042d739
  rdata   integral              32    'habcdd739
  rresp   integral              2     'h0
------------------------------------------------
UVM_INFO ./tb/sequence/axi_read_sequence.sv(20) @ 165000: uvm_test_top.env.read_agent.sequencer@@seq [axi_read_sequence] Read transaction sent: addr=0xc042d739
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 165000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
