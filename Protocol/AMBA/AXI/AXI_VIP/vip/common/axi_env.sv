`ifndef AXI_ENV_SV
`define AXI_ENV_SV

class axi_env extends uvm_env;
    `uvm_component_utils(axi_env)

    axi_master_agent        agt_mst;
    axi_slave_agent         agt_slv;
    axi_scoreboard          scb;
    axi_coverage            cov;
    virtual axi_interface   vif;

    function new(string name = "axi_env", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Type override is written in master/slave env
        agt_mst = axi_master_agent::type_id::create("agt_mst", this);
        agt_slv = axi_slave_agent::type_id::create("agt_slv", this);

        scb = axi_scoreboard::type_id::create("scb", this);
        cov = axi_coverage::type_id::create("cov", this);

        if (!uvm_config_db #(virtual axi_interface)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name()))

        uvm_config_db #(virtual axi_interface.master)::set(this, "agt_mst.*", "vif", vif);
        uvm_config_db #(virtual axi_interface.slave)::set(this, "agt_slv.*", "vif", vif);

        // agent mode will always be UVM_ACTIVE in this project
        uvm_config_db #(uvm_active_passive_enum)::set(this, "agt_mst", "agt_mode", UVM_ACTIVE);
        uvm_config_db #(uvm_active_passive_enum)::set(this, "agt_slv", "agt_mode", UVM_ACTIVE);

    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        // SCB connection
        agt_mst.mon.port.connect(scb.imp);

        // COV connection
        agt_mst.mon.port.connect(cov.analysis_export);
    endfunction

endclass

`endif
