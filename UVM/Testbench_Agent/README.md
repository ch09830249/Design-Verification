# UVM Agent
![image](https://github.com/user-attachments/assets/3f1a44ce-0c99-44cf-90d3-cee6806a1fb2)
* An **agent** encapsulates a **Sequencer**, **Driver** and **Monitor** into a single entity by **instantiating** and **connecting the components together** via TLM interfaces. An agent can also have configuration options like the type of UVM agent (active/passive), knobs to turn on features such as functional coverage, and other similar parameters.
* Types of Agents   (可以透過 get_is_active() 得知)
   * Active:
      * Instantiates all three components [Sequencer, Driver, Monitor]
      * **Enables data to be driven to DUT via driver**
   * Passive:
      * Only instantiate the monitor  Used for checking and coverage only
      * **Useful when there's no data item to be driven to DUT**
# Class Hierarchy
![image](https://github.com/user-attachments/assets/5e4c4977-5201-4527-bb3b-6aaa3644e6fd)
# 建立 UVM Agent 的步驟
* Create a custom class inherited from uvm_agent, register with factory and call new
```
// my_agent is user-given name for this class that has been derived from "uvm_agent"
class my_agent extends uvm_agent;

    // [Recommended] Makes this agent more re-usable
    `uvm_component_utils (my_agent)

    // This is standard code for all components
    function new (string name = "my_agent", uvm_component parent = null);
      super.new (name, parent);
    endfunction

    // Code for rest of the steps come here
endclass
```
* Instantiate agent components
```
// Create handles to all agent components like driver, monitor and sequencer
// my_driver, my_monitor and agent_cfg are custom classes assumed to be defined
// Agents can be configured via a configuration object that can be passed in from the test
   my_driver                  m_drv0;
   my_monitor                 m_mon0;
   uvm_sequencer #(my_data)   m_seqr0;
   agent_cfg                  m_agt_cfg;
```
* Instantiate and build components
```
virtual function void build_phase (uvm_phase phase);
// 這裡特別針對 active 有不同的處理
// If this UVM agent is active, then build driver, and sequencer
         if (get_is_active()) begin
            m_seqr0 = uvm_sequencer#(my_data)::type_id::create ("m_seqr0", this);   // 只有 Active agent 需要驅動 DUT, 所以需要 sequencer 和 driver
            m_drv0 = my_driver::type_id::create ("m_drv0", this);
         end

         // Both active and passive agents need a monitor
         m_mon0 = my_monitor::type_id::create ("m_mon0", this);   // monitor 都要

         //[Optional] Get any agent configuration objects from uvm_config_db
      endfunction
```
* Connect agent components together
```
virtual function void connect_phase (uvm_phase phase);

// Connect the driver to the sequencer if this agent is Active
         if (get_is_active())
            m_drv0.seq_item_port.connect (m_seqr0.seq_item_export);      // 如果是 active, driver 就要接收來自 sequencer 的 transaction 所以要連接
      endfunction
```
