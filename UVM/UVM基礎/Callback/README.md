# Callback
* The uvm_callback class serves as the base class for user-defined callback classes. Typically, a component developer creates an **application-specific callback class** by extending this base class. In the derived class, the developer defines one or more virtual methods, collectively known as the callback interface, which provide the hooks that users can override.
![image](https://github.com/user-attachments/assets/1cf6b7b7-119a-49be-9e60-f543a08f28e3)
* A callback is useful because it allows a **flexible and modular way to modify or extend the behavior of a system without altering the original code**. Callbacks decouple the code that triggers an action from the code that defines the action itself. It is required in scenarios where customization, or dynamic behavior is necessary.

## Example
* Let's create a callback mechanism that allows us to extend the behavior of a  monitor by adding custom code to a call_pre_check() and call_post_check() methods.
1. Define the Callback Class 將需要實作的 function 
```
class my_monitor_cb extends uvm_callback;	// 繼承 uvm_callback
  `uvm_object_utils(my_monitor_cb)		// 註冊該 callback

  function new(string name="my_monitor_cb");
    super.new(name);
  endfunction

  // 定義 call_pre_check 和 call_post_check 兩個需要被實作的 function
  virtual function void call_pre_check();
    // Placeholder
  endfunction

  virtual function void call_post_check();
    // Placeholder
  endfunction

endclass
```
2. Define a Custom Callback
```
class custom_monitor_cb extends my_monitor_cb;		// 繼承剛剛定義好的 prototype, 實作裡面的 function
  `uvm_object_utils(custom_monitor_cb)			// 註冊該 callback
  function new(string name="custom_monitor_cb");
    super.new(name);
  endfunction

  // Override the callback method with custom behavior	// Ovrride 實作 function
  virtual function void call_pre_check();
    `uvm_info(get_type_name(), $sformatf("[call_pre_check] start pre_check"), UVM_LOW)
  endfunction

  virtual function void call_post_check();
    `uvm_info(get_type_name(), $sformatf("[call_post_check] start post_check"), UVM_LOW)
  endfunction

endclass
```
3. Add Callback Hooks and Register the Callback (在需要使用到該 function 的地方, 註冊該 callback 並且呼叫)
```
class my_monitor extends uvm_monitor;

  `uvm_component_utils(my_monitor)
  function new(string name="my_monitor", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  // Register the callback class for this component
  `uvm_register_cb(my_monitor, my_monitor_cb)		// 註冊 callback, 參數1: 使用 callback 的 component, 參數2: 欲使用 callback 的 base class (PS: 記得要註冊其 base class)

  // Method that processes a transaction and uses the callback
  function void check_transaction();
    // Call the registered callback(s)
    `uvm_do_callbacks(my_monitor, my_monitor_cb, call_pre_check());	// 呼叫已註冊的 callback, 參數1: 使用 callback 的 component, 參數2: 欲使用 callback 的 base class, 參數3: 欲呼叫的 function

    // Normal checking logic
    `uvm_info("MONITOR", "Checking transaction", UVM_MEDIUM)

    // Or use a callback macro
    `uvm_do_callbacks(my_monitor, my_monitor_cb, call_post_check());
  endfunction

  // Run phase where the transaction check happens
  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);

    // Call the checking function, which triggers callbacks
    check_transaction();
  endtask
endclass
```
4. Register the Callback in the Test (在 testcase 中, 註冊該 testcase 要使用哪種 custom monitor callback)
```
class my_test extends uvm_test;
  `uvm_component_utils(my_test)
  function new(string name="my_test", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  my_monitor          mon;
  custom_monitor_cb   my_cb;	// 創建剛剛繼承 my_monitor_cb 的子類 custom_monitor_cb

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create the monitor
    mon = my_monitor::type_id::create("mon", null);

    // Create and register the custom callback
    my_cb = custom_monitor_cb::type_id::create("my_cb");	// 實例化 custom_monitor_cb
    uvm_callbacks#(my_monitor)::add(mon, my_cb);		// 將 custom_monitor_cb 與 my_monitor 中的 my_monitor_cb 連結

  endfunction
endclass
```
Finally create a module to run the test.  
```
module tb;
  initial
    run_test("my_test");
endmodule
```
```
UVM_INFO @ 0: reporter [RNTST] Running test my_test...
UVM_INFO testbench.sv(60) @ 0: reporter [custom_monitor_cb] [call_pre_check] start pre_check
UVM_INFO testbench.sv(37) @ 0: mon [MONITOR] Checking transaction
UVM_INFO testbench.sv(64) @ 0: reporter [custom_monitor_cb] [call_post_check] start post_check
UVM_INFO /xcelium23.09/tools/methodology/UVM/CDNS-1.2/sv/src/base/uvm_report_server.svh(847) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
