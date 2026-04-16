`ifndef APB_ENV_SV
`define APB_ENV_SV

class apb_env extends uvm_env;
    `uvm_component_utils(apb_env)

    apb_master_agent        agt_mst;
    apb_slave_agent         agt_slv;
    apb_scoreboard          scb;
    apb_coverage            cov;

    virtual apb_interface   vif;

    uvm_tlm_analysis_fifo #(apb_seq_item)   fifo;

    function new ( string name = "apb_env", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        fifo = new("fifo", this);
        
        // Type override is written in master/slave env
        agt_mst = apb_master_agent :: type_id :: create ("agt_mst", this);
        agt_slv = apb_slave_agent :: type_id :: create ("agt_slv", this);

        scb = apb_scoreboard :: type_id :: create ("scb", this);
        cov = apb_coverage :: type_id :: create ("cov", this);

        if ( !uvm_config_db #(virtual apb_interface) :: get (this, "", "vif", vif) )
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name() ))

        uvm_config_db #(virtual apb_interface.master) :: set (this, "agt_mst.*", "vif", vif);
        uvm_config_db #(virtual apb_interface.slave) :: set (this, "agt_slv.*", "vif", vif);

        // agent mode will always be UVM_ACTIVE in this project
        uvm_config_db #(uvm_active_passive_enum) :: set (this, "agt_mst", "agt_mode", UVM_ACTIVE);
        uvm_config_db #(uvm_active_passive_enum) :: set (this, "agt_slv", "agt_mode", UVM_ACTIVE);

        // Set fifo for apb_slave_seq
        uvm_config_db #(uvm_tlm_analysis_fifo #(apb_seq_item)) :: set (this, "*", "fifo", fifo);
    endfunction

    function void connect_phase ( uvm_phase phase );
        super.connect_phase(phase);

        // SCB connection
        agt_mst.mon.port.connect(scb.imp);

        // COV connection - slave mon connection is unnecessary
        agt_mst.mon.port.connect(cov.analysis_export);

        // slave mon -> fifo -> slave seq -> slave driver -> vif
        agt_slv.mon.port.connect(fifo.analysis_export);
    endfunction
endclass

`endif
