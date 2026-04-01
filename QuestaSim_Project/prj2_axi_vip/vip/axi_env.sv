// 用於統合 master/slave agent
class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_agent master_agent;
    axi_agent slave_agent;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        master_agent = axi_agent::type_id::create("master_agent", this);
        slave_agent  = axi_agent::type_id::create("slave_agent", this);

        uvm_config_db#(bit)::set(this, "master_agent", "is_master", 1);
        uvm_config_db#(bit)::set(this, "slave_agent",  "is_master", 0);

        uvm_config_db#(uvm_active_passive_enum)::set(this, "master_agent", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "slave_agent",  "is_active", UVM_PASSIVE);
    endfunction
endclass
