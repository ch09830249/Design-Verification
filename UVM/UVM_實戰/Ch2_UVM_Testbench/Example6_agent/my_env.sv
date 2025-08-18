/*
    1. 只有 uvm_component 才能作為樹的結點，像 my_transaction 這種使用 uvm_object_utils 宏實現的類別是不能作為 UVM 樹的結點的。
    2. UVM 要求 UVM 樹最晚在 build_phase 時段完成，如果在 build_phase 後的某個 phase 實例化一個 component，UVM 會給出以下錯誤提示。
       那麼是不是只能在 build_phase 中執行實例化的動作呢？答案是否定的。
       其實還可以在 new 函數中執行實例化的動作
       EX: 可以在 my_agent 的 new 函數中實例化 driver 和 monitor
*/
`include "my_agent.sv"
class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
        `uvm_info("my_env", "my_envs is new", UVM_LOW);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        `uvm_info("my_env", "my_env build phase!!", UVM_LOW);
        // drv = my_driver::type_id::create("drv", this);
        // i_mon = my_monitor::type_id::create("i_mon", this);
        // o_mon = my_monitor::type_id::create("o_mon", this);
        /*
            這裡透過 config table 對 i_agt 和 o_agt 設定為不同 mode
        */
        uvm_config_db#(uvm_active_passive_enum)::set(this, "i_agt", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "o_agt", "is_active", UVM_PASSIVE);
        /*
            完成 i_agt 和 o_agt 的聲明後，在 my_env 的 build_phase 中對它們進行實例化後，需要指定各自的工作模式是 active 模式還是 passive 模式
        */
        i_agt = my_agent::type_id::create("i_agt", this);
        o_agt = my_agent::type_id::create("o_agt", this);
    endfunction

    `uvm_component_utils(my_env)

endclass
