# UVM Environment
![image](https://github.com/user-attachments/assets/f36823ec-b2d5-4d66-aa23-011288643e38)
* A UVM environment 包含多個 agents for different interfaces, scoreboard, functional coverage collector 和 additional checkers
# Class Hierarchy
![image](https://github.com/user-attachments/assets/9d90374a-75e1-406c-b0f3-72123bfb24cc)
# 建立 UVM Env 的步驟
* Create a custom class inherited from uvm_env, register with factory, and callnew
```
  // my_env is user-given name for this class that has been derived from "uvm_env"
class my_env extends uvm_env;   // 繼承 uvm_env

    // [Recommended] Makes this driver more re-usable
    `uvm_component_utils (my_env)   // 註冊該類別

    // This is standard code for all components
    function new (string name = "my_env", uvm_component parent = null);
      super.new (name, parent);
    endfunction

    // Code for rest of the steps come here
endclass
```
* Declare and build verification components
```
// apb_agnt and other components are assumed to be user-defined classes that already exist in TB
apb_agnt	   m_apb_agnt;         // 這裡創建 apb_agent, function coverage, scoreboard, env configuration 的 handle
func_cov 	m_func_cov;
scbd 		   m_scbd;
env_cfg 	   m_env_cfg;

// Build components within the "build_phase"
virtual function void build_phase (uvm_phase phase);      // 在 build phase 透過 factory 機制實例化
	super.build_phase (phase);
	m_apb_agnt = apb_agnt::type_id::create ("m_apb_agnt", this);
	m_func_cov = func_cov::type_id::create ("m_func_cov", this);
	m_scbd     = scbd::type_id::create ("m_scbd", this);

	// [Optional] Collect configuration objects from the test class if applicable
	if (uvm_config_db #(env_cfg)::get(this, "", "env_cfg", m_env_cfg))      // 這裡是將之前在上一層 test 對此 env 的 configuration object 取出, 用我們 handle 去接 
		`uvm_fatal ("build_phase", "Did not get a configuration object for env")

	// [Optional] Pass other configuration objects to sub-components via uvm_config_db
endfunction
```
* Connect verification components together
```
virtual function void connect_phase (uvm_phase phase);      // 在 env class 中的 connect phase 去連接各個組件
	// A few examples:
	// Connect analysis ports from agent to the scoreboard
	// Connect functional coverage component analysis ports
	// ...
endfunction
```
# 連接組件
![image](https://github.com/user-attachments/assets/d09ac3d9-fa8c-427d-bb94-440eecc25fd7)
```
class my_env extends uvm_env ;

   `uvm_component_utils (my_env)

   my_agent             m_agnt0;
   my_scoreboard        m_scbd0;

   function new (string name, uvm_component parent);
      super.new (name, parent);
   endfunction : new

   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      m_agnt0 = my_agent::type_id::create ("my_agent", this);
      m_scbd0 = my_scoreboard::type_id::create ("my_scoreboard", this);
   endfunction : build_phase

   virtual function void connect_phase (uvm_phase phase);
      // Connect the scoreboard with the agent
      m_agnt0.m_mon0.item_collected_port.connect (m_scbd0.data_export);   // 這裡連接 scoreboard 和 agent
   endfunction

endclass
```
# UVM Environment Example
```
class my_top_env extends uvm_env;
   `uvm_component_utils (my_env)

   agent_apb          m_apb_agt;
   agent_wishbone     m_wb_agt;

   env_register       m_reg_env;            // env 內的 env, Nested env
   env_analog         m_analog_env [2];

   scoreboard         m_scbd;

   function new (string name = "my_env", uvm_component parent);
      super.new (name, parent);
   endfunction

   virtual function void build_phase (uvm_phase phase);
      super.build_phase (phase);
      // Instantiate different agents and environments here
      m_apb_agt = agent_apb::type_id::create ("m_apb_agt", this);
      m_wb_agt  = agent_wishbone::type_id::create ("m_wb_agt", this);

      m_reg_env = env_register::type_id::create ("m_reg_env", this);
      foreach (m_analog_env[i])
        m_analog_env[i] = env_analog::type_id::create ($sformatf("m_analog_env%0d",m_analog_env[i]), this);

      m_scbd = scoreboard::type_id::create ("m_scbd", this);
   endfunction

   virtual function void connect_phase (uvm_phase phase);
   	   // Connect between different environments, agents, analysis ports, and scoreboard here
   endfunction
endclass
```

