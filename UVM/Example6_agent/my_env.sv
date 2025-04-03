class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
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