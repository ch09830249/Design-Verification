// 用於統合 master/slave agent
class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_agent           active_agent;
    axi_agent           passive_agent;
    axi_scoreboard      scoreboard;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        active_agent        = axi_agent::type_id::create("active_agt", this);
        passive_agent       = axi_agent::type_id::create("passive_agt", this);
        scoreboard          = axi_scoreboard::type_id::create("scb", this);

        // uvm_config_db#(bit)::set(this, "master_agt*", "is_master", 1);    // 自己 + 所有子層
        // uvm_config_db#(bit)::set(this, "slave_agt*",  "is_master", 0);    

        uvm_config_db#(uvm_active_passive_enum)::set(this, "active_agt", "is_active", UVM_ACTIVE);
        uvm_config_db#(uvm_active_passive_enum)::set(this, "passive_agt",  "is_active", UVM_PASSIVE);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        active_agent.monitor.ap.connect(scoreboard.fifo.analysis_export);
    endfunction
endclass
