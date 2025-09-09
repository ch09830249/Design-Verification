# command line
xrun -uvm -access +r ./tb/ahb_write_top.sv ./rtl/ahb_write_slave.sv -f ./tb/ahb_write_flist.f
# xrun.log
<img width="1759" height="320" alt="image" src="https://github.com/user-attachments/assets/1aeac653-0ebe-45a9-8dc1-228a4e090460" />

```
UVM_INFO @ 0: reporter [RNTST] Running test ahb_write_test...
UVM_INFO ./tb/agent/ahb_write_driver.sv(20) @ 0: uvm_test_top.env.agt.drv [ahb_write_driver] Write data transaction
-----------------------------------------------------------------------------------
Name                           Type             Size  Value
-----------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3672
  addr                         integral         32    'h3e331a0c
  data                         integral         32    'hd8dfe655
  size                         integral         3     'h2
  begin_time                   time             64    0
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           29    uvm_test_top.env.agt.seqr.seq
  sequencer                    string           25    uvm_test_top.env.agt.seqr
-----------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_write_driver.sv(20) @ 15000: uvm_test_top.env.agt.drv [ahb_write_driver] Write data transaction
-----------------------------------------------------------------------------------
Name                           Type             Size  Value
-----------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3736
  addr                         integral         32    'h7b1e9aec
  data                         integral         32    'h36867f7a
  size                         integral         3     'h2
  begin_time                   time             64    15000
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           29    uvm_test_top.env.agt.seqr.seq
  sequencer                    string           25    uvm_test_top.env.agt.seqr
-----------------------------------------------------------------------------------
UVM_INFO ./tb/agent/ahb_write_driver.sv(20) @ 35000: uvm_test_top.env.agt.drv [ahb_write_driver] Write data transaction
-----------------------------------------------------------------------------------
Name                           Type             Size  Value
-----------------------------------------------------------------------------------
tr                             ahb_transaction  -     @3735
  addr                         integral         32    'ha55197d0
  data                         integral         32    'hfaa622eb
  size                         integral         3     'h2
  begin_time                   time             64    35000
  depth                        int              32    'd2
  parent sequence (name)       string           3     seq
  parent sequence (full name)  string           29    uvm_test_top.env.agt.seqr.seq
  sequencer                    string           25    uvm_test_top.env.agt.seqr
-----------------------------------------------------------------------------------
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 55000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase

```
