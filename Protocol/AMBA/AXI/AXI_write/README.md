# command line
xrun -uvm -access +r ./tb/axi_write_top.sv ./rtl/axi_write_slave.sv -f ./tb/axi_write_flist.f
# xrun.log
<img width="1554" height="363" alt="image" src="https://github.com/user-attachments/assets/2b5ac68f-ae89-46e7-8f62-438b31233ca0" />
<img width="749" height="335" alt="image" src="https://github.com/user-attachments/assets/6ee42088-d288-4d32-a7e0-93db84ef4c9e" />

```
UVM_INFO @ 0: reporter [RNTST] Running test axi_write_test...
-----------------------------------------------
Name    Type                   Size  Value
-----------------------------------------------
tr      axi_write_transaction  -     @3568
  addr  integral               32    'h3e331a0e
  data  integral               32    'hd8dfe655
-----------------------------------------------
UVM_INFO ./tb/agent/axi_write_driver.sv(38) @ 45000: uvm_test_top.env.write_agent.driver [DRV] BRESP: 0
-----------------------------------------------
Name    Type                   Size  Value
-----------------------------------------------
tr      axi_write_transaction  -     @3602
  addr  integral               32    'h7b1e9aef
  data  integral               32    'h36867f7a
-----------------------------------------------
UVM_INFO ./tb/agent/axi_write_driver.sv(38) @ 85000: uvm_test_top.env.write_agent.driver [DRV] BRESP: 0
-----------------------------------------------
Name    Type                   Size  Value
-----------------------------------------------
tr      axi_write_transaction  -     @3584
  addr  integral               32    'ha55197d1
  data  integral               32    'hfaa622eb
-----------------------------------------------
UVM_INFO ./tb/agent/axi_write_driver.sv(38) @ 125000: uvm_test_top.env.write_agent.driver [DRV] BRESP: 0
UVM_INFO /home/project/eda/pkgs/cadence/xcelium/v23.03/tools/methodology/UVM/CDNS-1.1d/sv/src/base/uvm_objection.svh(1268) @ 135000: reporter [TEST_DONE] 'run' phase is ready to proceed to the 'extract' phase
```
