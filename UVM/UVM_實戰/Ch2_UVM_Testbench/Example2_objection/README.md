# xrun.log
因為改用 uvm 架構去跑, 所以加了 raise/drop objection 就可以了!!! 所以有 wave form 了
<img width="1918" height="386" alt="image" src="https://github.com/user-attachments/assets/92f10eba-4a90-41aa-9cd6-1f1fc1bd9d56" />

```
UVM_INFO my_driver.sv(11) @ 0: uvm_test_top [my_driver] new is called
UVM_INFO @ 0: reporter [RNTST] Running test my_driver...
UVM_INFO my_driver.sv(23) @ 0: uvm_test_top [my_driver] main_phase is called
UVM_INFO my_driver.sv(32) @ 1300000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 1500000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 1700000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 1900000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 2100000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 2300000: uvm_test_top [my_driver] data is drived
......
UVM_INFO my_driver.sv(32) @ 51700000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 51900000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 52100000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(32) @ 52300000: uvm_test_top [my_driver] data is drived
UVM_INFO my_driver.sv(36) @ 52500000: uvm_test_top [my_driver] main_phase finished

```
