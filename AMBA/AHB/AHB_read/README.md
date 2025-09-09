# command line
xrun -uvm -access +r ./tb/ahb_read_top.sv ./rtl/ahb_read_slave.sv -f ./tb/ahb_read_flist.f

# xrun.log
<img width="1552" height="280" alt="image" src="https://github.com/user-attachments/assets/933ca586-2547-43b9-8d60-185ff10c6424" />

```
UVM_INFO @ 0: reporter [RNTST] Running test ahb_read_test...
-------------------------------------------------------------------------------------
Name                           Type             Size  Value
-------------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3657
  addr                         integral         32    'h3e330000
  data                         integral         32    'h0
  size                         integral         3     'h2
  begin_time                   time             64    0
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           31    uvm_test_top.env.agent.seqr.seq
  sequencer                    string           27    uvm_test_top.env.agent.seqr
-------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 35000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3709
  addr  integral         32    'h3e330000
  data  integral         32    'h0
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 45000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3690
  addr  integral         32    'h3e330000
  data  integral         32    'h3e33a5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/sequence/ahb_read_sequence.sv(19) @ 45000: uvm_test_top.env.agent.seqr@@seq [AHB_SEQ] Read Data: 0x00000000
-------------------------------------------------------------------------------------
Name                           Type             Size  Value
-------------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3694
  addr                         integral         32    'h7b1e0000
  data                         integral         32    'h0
  size                         integral         3     'h2
  begin_time                   time             64    45000
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           31    uvm_test_top.env.agent.seqr.seq
  sequencer                    string           27    uvm_test_top.env.agent.seqr
-------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 65000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3740
  addr  integral         32    'h7b1e0000
  data  integral         32    'h3e33a5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 75000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3730
  addr  integral         32    'h7b1e0000
  data  integral         32    'h7b1ea5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/sequence/ahb_read_sequence.sv(19) @ 75000: uvm_test_top.env.agent.seqr@@seq [AHB_SEQ] Read Data: 0x3e33a5a5
-------------------------------------------------------------------------------------
Name                           Type             Size  Value
-------------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3738
  addr                         integral         32    'ha5510000
  data                         integral         32    'h0
  size                         integral         3     'h2
  begin_time                   time             64    75000
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           31    uvm_test_top.env.agent.seqr.seq
  sequencer                    string           27    uvm_test_top.env.agent.seqr
-------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 95000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3698
  addr  integral         32    'ha5510000
  data  integral         32    'h7b1ea5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 105000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3680
  addr  integral         32    'ha5510000
  data  integral         32    'ha551a5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/sequence/ahb_read_sequence.sv(19) @ 105000: uvm_test_top.env.agent.seqr@@seq [AHB_SEQ] Read Data: 0x7b1ea5a5
-------------------------------------------------------------------------------------
Name                           Type             Size  Value
-------------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3707
  addr                         integral         32    'ha9230000
  data                         integral         32    'h0
  size                         integral         3     'h2
  begin_time                   time             64    105000
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           31    uvm_test_top.env.agent.seqr.seq
  sequencer                    string           27    uvm_test_top.env.agent.seqr
-------------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 125000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3690
  addr  integral         32    'ha9230000
  data  integral         32    'ha551a5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/agent/ahb_read_monitor.sv(26) @ 135000: uvm_test_top.env.agent.mon [ahb_read_monitor] Monitor read data
-----------------------------------------
Name    Type             Size  Value
-----------------------------------------
tr      ahb_transaction  -     @3725
  addr  integral         32    'ha9230000
  data  integral         32    'ha923a5a5
  size  integral         3     'h2
-----------------------------------------
UVM_INFO ./tb/sequence/ahb_read_sequence.sv(19) @ 135000: uvm_test_top.env.agent.seqr@@seq [AHB_SEQ] Read Data: 0xa551a5a5
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 135000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
