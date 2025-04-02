class my_env extends uvm_env;

    my_agent i_agt;
    my_agent o_agt;

    function new(string name = "my_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        i_agt = my_agent::type_id::create("i_agt", this);
        o_agt = my_agent::type_id::create("o_agt", this);
        i_agt.is_active = UVM_ACTIVE;
        o_agt.is_active = UVM_PASSIVE;
    endfunction

    `uvm_component_utils(my_env)

    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.drv", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.drv", "vif2", output_if);
    end

endclass