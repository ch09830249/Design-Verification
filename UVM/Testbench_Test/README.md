# UVM Test
![image](https://github.com/user-attachments/assets/3a89ce7c-22b6-47f1-a156-b659d11885de)
* Testcase 是一種 pattern 用於檢查和驗證 design 特定 feature 和 functionality。Test plan 列出所有需要驗證的 feature 和 functional items，然後每個測試需要涵蓋每個功能。
* Testcase 可以設置不同的 configuration (EX: 改變 configuration table 中的變數), sequence 和 sequencer 也可以設定或更換, enable/disable Agent
  * PS: 分層的目的是為了 code reuse
# Class Hierarchy
![image](https://github.com/user-attachments/assets/eaefa44a-a55d-40b3-aed6-08e74dfebeda)
# 建立 UVM Test 的步驟
  * Create a custom class inherited from uvm_test, register it with factory and call function new
  ```
  // Step 1: Declare a new class that derives from "uvm_test"
  // my_test is user-given name for this class that has been derived from "uvm_test" 
  class my_test extends uvm_test;    // my_test 為繼承 uvm_test 的子類
  
      // [Recommended] Makes this test more re-usable
      `uvm_component_utils (my_test)  // 註冊該 component
  
      // This is standard code for all components
      function new (string name = "my_test", uvm_component parent = null);  // 實作其建構子, uvm_component parent 是建立 UVM 結構樹用的
        super.new (name, parent);
      endfunction
  
      // Code for rest of the steps come here
  endclass
  ```
  * Declare other environments and verification components and build them
  ```
  // Step 2: Declare other testbench components - my_env and my_cfg are assumed to be defined
      // 這裡主要是建立其他 components 的 handle
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
  ```
    // [Recommended] By this phase, the environment is all set up so its good to just print the topology for debug
      // 在 end_of_elaboration_phase 中印出 topology 確認 components 之間的連接
      virtual function void end_of_elaboration_phase (uvm_phase phase);
         uvm_top.print_topology ();
      endfunction
  ```
* Start a virtual sequence
  ```
    // Start a virtual sequence or a normal sequence for this particular test
    // Override run phase
    virtual task run_phase (uvm_phase phase);
    
    	// Create and instantiate the sequence
    	my_seq m_seq = my_seq::type_id::create ("m_seq");
    
    	// Raise objection - else this test will not consume simulation time*
    	phase.raise_objection (this);
    
    	// Start the sequence on a given sequencer
    	m_seq.start (m_env.seqr);
    
    	// Drop objection - else this test will not finish
    	phase.drop_objection (this);
    endtask
  ```
# 
