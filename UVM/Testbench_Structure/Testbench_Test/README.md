# UVM Test
![image](https://github.com/user-attachments/assets/3a89ce7c-22b6-47f1-a156-b659d11885de)
* A testcase is a pattern to **check and verify specific features and functionalities of a design**. A verification plan lists all the features and other functional items that needs to be verified, and the tests neeeded to cover each of them.
* We put the entire testbench into a container called an Environment, and use the same environment with **a different configuration for each test**.
* Each testcase can **override**, **tweak knobs**, **enable/disable agents**, **change variable values in the configuration table** and **run different sequences on many sequencers** in the verification environment.
# Class Hierarchy
![image](https://github.com/user-attachments/assets/eaefa44a-a55d-40b3-aed6-08e74dfebeda)
# 建立 UVM Test 的步驟
* Create a custom class inherited from **uvm_test**, register it with factory and call function new
```
// Step 1: Declare a new class that derives from "uvm_test"
// my_test is user-given name for this class that has been derived from "uvm_test" 
class my_test extends uvm_test;    // my_test 為繼承 uvm_test 的子類

    // [Recommended] Makes this test more re-usable
    `uvm_component_utils (my_test)  // 向 factory 註冊該 component

    // This is standard code for all components
    function new (string name = "my_test", uvm_component parent = null);  // 實作其建構子, uvm_component parent 是建立 UVM 結構樹用的
      super.new (name, parent);
    endfunction

    // Code for rest of the steps come here
endclass
```
* Declare other environments and verification components and build them
  * Configuration objection
    * Testbench environment component called **m_top_env** and its **configuration object** is created during the build_phase
    * Setup according to the needs of the test.
    * Placed it into the configuration database using uvm_config_db so that **other testbench components within this environment can access the object** and **configure sub components accordingly**. 
(在 env 底下的 component 都可以藉由 configuration database 去取得這個 env 的設置資訊, 或是根據 env cfg 來設置 sub components)
```
// Step 2: Declare other testbench components - my_env and my_cfg are assumed to be defined
    // 這裡主要是建立其他 components 的 handle (env 和 cfg for env)
    my_env   m_top_env;              // Testbench environment that contains other agents, register models, etc
    my_cfg   m_cfg0;                 // Configuration object to tweak the environment for this test

    // Instantiate and build components declared above
    // 在 build phase 實例化以上的 components
    virtual function void build_phase (uvm_phase phase);
        super.build_phase (phase);

        // [Recommended] Instantiate components using "type_id::create()" method instead of new()
        // 這裡都是透過 factory 機制去做實例化, 而非 new
        m_top_env  = my_env::type_id::create ("m_top_env", this);   // 第一個參數為名稱, 第二個參數設置 parent, 這裡就是設置 my_test 為 m_top_env 和 m_cfg0 的 parent
        m_cfg0     = my_cfg::type_id::create ("m_cfg0", this);

        // [Optional] Configure testbench components if required, get virtual interface handles, etc
        // 設定 testbench components`
        set_cfg_params ();

        // [Recommended] Make the cfg object available to all components in environment/agent/etc
        // 設定在 configuration table 的變數
        uvm_config_db #(my_cfg) :: set (this, "m_top_env.my_agent", "m_cfg0", m_cfg0);
    endfunction
```
* Print UVM topology if required
  * print_topology()
    * The UVM topology task print_topology displays all instantiated components in the environment and helps in debug and to identify if any component got left out.
```
  // [Recommended] By this phase, the environment is all set up so its good to just print the topology for debug
    // 在 end_of_elaboration_phase 中印出 topology 確認 components 之間的連接
    virtual function void end_of_elaboration_phase (uvm_phase phase);
        uvm_top.print_topology ();
    endfunction
```
* Start a virtual sequence
  * objection 機制: UVM 透過 objection 機制來控制驗證平台的關閉, 在每個 phase 中, UVM 會檢查是否有 objection 被 raise (raise_objection)
    * 如果有, 則會等待該 objection 被註銷才停止 simulation, 如果沒有, 則不會消耗 simulation time, 該 phase 立即結束
    * raise_objection 和 drop_objection 通常成雙成對出現
    * raise_objection 要放在第一個消耗 simulation time 的語句之前
```
  // Start a virtual sequence or a normal sequence for this particular test
  // Override run phase 請覆寫  run phase
  virtual task run_phase (uvm_phase phase);
  
    // Create and instantiate the sequence
    my_seq m_seq = my_seq::type_id::create ("m_seq");  // 建立 sequence

    /*
    UVM 透過 objection 機制來控制驗證平台的關閉, 在每個 phase 中, UVM 會檢查是否有 objection 被 raise (raise_objection),
    如果有, 則會等待該 objection 被註銷才停止 simulation
    如果沒有, 則不會消耗 simulation time, 該 phase 立即結束
    */
    // Raise objection - else this test will not consume simulation time*
    phase.raise_objection (this);
  
    // Start the sequence on a given sequencer
    m_seq.start (m_env.seqr);   // sequence 產生 transaction 並發送
  
    // Drop objection - else this test will not finish  若不 drop 則會一直消耗 simulation time
    phase.drop_objection (this);
  endtask
```
# 如何跑一個 UVM test
* A test is usually started within **testbench top** by a task called **run_test**. (通常透過 top 中的 run_test 這個 task 啟動)
* This global task should be supplied with the name of user-defined UVM test that needs to be started.
  * If the argument to run_test is **blank**, it is necessary to specify the testname via command-line options to the simulator using **+UVM_TESTNAME**.
    (可以在透過 command line 的 option 去做設定)
```
// Specify the testname as an argument to the run_test () task
initial begin
   run_test ("base_test");
end
```
* 可以 override task run_test
```
// This is a global task that gets the UVM root instance and
// starts the test using its name. This task is called in tb_top
task run_test (string test_name="");
  uvm_root top;
  uvm_coreservice_t cs;
  cs = uvm_coreservice_t::get();
  top = cs.get_root();
  top.run_test(test_name);
endtask
```
* Command line 啟動 test
```
// Command-line arguments for an EDA simulator
$> [simulator] -f list +UVM_TESTNAME=base_test
```
# UVM Base Test Example
* A test sequence object is built and started on the environment virtual sequencer using its start method.
```
// Step 1: Declare a new class that derives from "uvm_test"
class base_test extends uvm_test;

	  // Step 2: Register this class with UVM Factory
   `uvm_component_utils (base_test)

   // Step 3: Define the "new" function
   function new (string name, uvm_component parent = null);
      super.new (name, parent);
   endfunction

   // Step 4: Declare other testbench components
   my_env   m_top_env;              // Testbench environment
   my_cfg   m_cfg0;                 // Configuration object


   // Step 5: Instantiate and build components declared above
   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);

      // [Recommended] Instantiate components using "type_id::create()" method instead of new()
      m_top_env  = my_env::type_id::create ("m_top_env", this);
      m_cfg0     = my_cfg::type_id::create ("m_cfg0", this);

      // [Optional] Configure testbench components if required
      set_cfg_params ();

      // [Optional] Make the cfg object available to all components in environment/agent/etc
      uvm_config_db #(my_cfg) :: set (this, "m_top_env.my_agent", "m_cfg0", m_cfg0);
   endfunction

   // [Optional] Define testbench configuration parameters, if its applicable
   virtual function void set_cfg_params ();
      // Get DUT interface from top module into the cfg object
      if (! uvm_config_db #(virtual dut_if) :: get (this, "", "dut_if", m_cfg0.vif)) begin
         `uvm_error (get_type_name (), "DUT Interface not found !")
      end

      // Assign other parameters to the configuration object that has to be used in testbench
      m_cfg0.m_verbosity    = UVM_HIGH;
      m_cfg0.active         = UVM_ACTIVE;
   endfunction

	  // [Recommended] By this phase, the environment is all set up so its good to just print the topology for debug
   virtual function void end_of_elaboration_phase (uvm_phase phase);
      uvm_top.print_topology ();
   endfunction

   function void start_of_simulation_phase (uvm_phase phase);
      super.start_of_simulation_phase (phase);

      // [Optional] Assign a default sequence to be executed by the sequencer or look at the run_phase ...
      uvm_config_db#(uvm_object_wrapper)::set(this,"m_top_env.my_agent.m_seqr0.main_phase",
                                       "default_sequence", base_sequence::type_id::get());

   endfunction

   // or [Recommended] start a sequence for this particular test
   virtual task run_phase (uvm_phase phase);
   	my_seq m_seq = my_seq::type_id::create ("m_seq");

   	super.run_phase(phase);
   	phase.raise_objection (this);
   	m_seq.start (m_env.seqr);
   	phase.drop_objection (this);
   endtask
endclass
```
# Derivative Tests
