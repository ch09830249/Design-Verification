# Factory
UVM factory is a mechanism to **improve flexibility and scalability** of the testbench by allowing the user to **substitute an existing class object by any of its inherited child class objects.**
For this purpose, the factory needs to know all the types of classes created within the testbench by a process called as registration. There are UVM macros that allow **classes to be registered with the factory**, and methods that allow **certain types and instances of class objects to be overridden by its derived types**.
* 註冊表: 所有向 factory 註冊的類別
* 替換表: 某個類別將會被哪個其子類別替換 (替換的目的是不同的 testcase 可能有不同的目的, 故可能需要替換另一個組件 (EX: Driver...))
* Override 的目的是我只需繼承父類別並客製化子類別, 然後在上層 (testcase 層) override 當前 testcase 的父類別都被子類別取代, 這樣下層 code 都可以不用修改以達到 code 重用性
![image](https://github.com/user-attachments/assets/3e1f45f5-6890-4630-bb17-b16775a114d9)
## Factory Override Methods
```
// Override all the objects of a particular type 將所有的某父類都被某子類取代
set_type_override_by_type ( uvm_object_wrapper original_type,
                            uvm_object_wrapper override_type,
                            bit replace=1);

set_type_override_by_name ( string original_type_name,
                            string override_type_name,
                            bit replace=1);

// Override a type within a particular instance 這是有指定特別範圍內, 某父類都被某子類取代
set_inst_override_by_type (uvm_object_wrapper original_type,
                           uvm_object_wrapper override_type,
                           string full_inst_path);

set_inst_override_by_name (string original_type_name,
                           string override_type_name,
                           string full_inst_path);
```
## Method Examples
```
// Define a base class agent
class base_agent extends uvm_agent;
  `uvm_component_utils(base_agent)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass

// Define child class that extends base agent
class child_agent extends base_agent;
  `uvm_component_utils(child_agent)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass

// Environment contains the agent
class base_env extends uvm_env;
  `uvm_component_utils(base_env)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  // 'm_agent' is a class handle to hold base_agent
  // type class objects
  base_agent m_agent;

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Use create method to request factory to return a base_agent
    // type of class object
    m_agent = base_agent::type_id::create("m_agent", this);	在沒有 override 的情況下, 這裡是實例化 base_agent 類別

    // Now print the type of the object pointing to by the 'm_agent' class handle
    `uvm_info("AGENT", $sformatf("Factory returned agent of type=%s, path=%s", m_agent.get_type_name(), m_agent.get_full_name()), UVM_LOW)
  endfunction
endclass
```
* Type override by Type/Name
```
class base_test extends uvm_test;
  `uvm_component_utils(base_test)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  base_env m_env;

  virtual function void build_phase(uvm_phase phase);
  	// Get handle to the singleton factory instance
    uvm_factory factory = uvm_factory::get();

    super.build_phase(phase);

    // Set factory to override 'base_agent' by 'child_agent' by type
    set_type_override_by_type(base_agent::get_type(), child_agent::get_type());     透過 get_type() 來 override, 表示 base_agent 被 child_agent 取代

    // Or set factory to override 'base_agent' by 'child_agent' by name
    // factory.set_type_override_by_name("base_agent", "child_agent");		    透過 class name override

    // Print factory configuration
    factory.print();

    // Now create environment
    m_env = base_env::type_id::create("m_env", this);	這裡實例化 child_agent 類別
  endfunction
endclass
```
```
UVM_INFO @ 0: reporter [RNTST] Running test base_test...
UVM_INFO /playground_lib/uvm-1.2/src/base/uvm_factory.svh(1645) @ 0: reporter [UVM/FACTORY/PRINT] 
#### Factory Configuration (*)

No instance overrides are registered with this factory

Type Overrides:

  Requested Type  Override Type
  --------------  -------------
  base_agent      child_agent				明顯看出 base_agent 被 child_agent 取代

All types registered with the factory: 54 total
  Type Name
  ---------
  base_agent
  base_env
  base_test
  child_agent
(*) Types with no associated type name will be printed as 

####


UVM_INFO testbench.sv(32) @ 0: uvm_test_top.m_env [AGENT] Factory returned agent of type=child_agent, path=uvm_test_top.m_env.m_agent
UVM_INFO /playground_lib/uvm-1.2/src/base/uvm_report_server.svh(847) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
* Instance override by Type/Name
```
class base_test extends uvm_test;
  `uvm_component_utils(base_test)
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  base_env m_env;

  virtual function void build_phase(uvm_phase phase);
  	// Get handle to the singleton factory instance
    uvm_factory factory = uvm_factory::get();

    super.build_phase(phase);

    // Set factory to override all instances under m_env of type 'base_agent' by 'child_agent'
    set_inst_override_by_type("m_env.*", base_agent::get_type(), child_agent::get_type());	在 env 底下的組件, base_agent 被 child_agent 取代

    // Or set factory to override all instances under 'm_env' called 'base_agent' by 'child_agent' by name
    // factory.set_inst_override_by_name("base_agent", "child_agent", {get_full_name(), ".m_env.*"});

    // Print factory configuration
    factory.print();

    // Now create environment
    m_env = base_env::type_id::create("m_env", this);
  endfunction
endclass
```
```
UVM_INFO @ 0: reporter [RNTST] Running test base_test...
UVM_INFO /playground_lib/uvm-1.2/src/base/uvm_factory.svh(1645) @ 0: reporter [UVM/FACTORY/PRINT] 
#### Factory Configuration (*)

Instance Overrides:

  Requested Type  Override Path         Override Type
  --------------  --------------------  -------------
  base_agent      uvm_test_top.m_env.*  child_agent		這裡很明顯有顯示 override 作用的範圍

No type overrides are registered with this factory

All types registered with the factory: 54 total
  Type Name
  ---------
  base_agent
  base_env
  base_test
  child_agent
(*) Types with no associated type name will be printed as 

####


UVM_INFO testbench.sv(32) @ 0: uvm_test_top.m_env [AGENT] Factory returned agent of type=child_agent, path=uvm_test_top.m_env.m_agent
UVM_INFO /playground_lib/uvm-1.2/src/base/uvm_report_server.svh(847) @ 0: reporter [UVM/REPORT/SERVER] 
--- UVM Report Summary ---
```
