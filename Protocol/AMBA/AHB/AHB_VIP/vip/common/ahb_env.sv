`ifndef AHB_ENV_SV
`define AHB_ENV_SV

class ahb_env extends uvm_env;
    `uvm_component_utils(ahb_env)

    ahb_master_agent        agt_mst;
    ahb_slave_agent         agt_slv;
    ahb_scoreboard          scb;
    ahb_coverage            cov;

    virtual ahb_interface   vif;

    uvm_tlm_analysis_fifo #(ahb_seq_item)   fifo;

    function new ( string name = "ahb_env", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);
        fifo = new("fifo", this);
        
        // Type override is written in master/slave env
        agt_mst = ahb_master_agent :: type_id :: create ("agt_mst", this);
        agt_slv = ahb_slave_agent :: type_id :: create ("agt_slv", this);

        scb = ahb_scoreboard :: type_id :: create ("scb", this);
        cov = ahb_coverage :: type_id :: create ("cov", this);

        if ( !uvm_config_db #(virtual ahb_interface) :: get (this, "", "vif", vif) )
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name() ))

        uvm_config_db #(virtual ahb_interface.master) :: set (this, "agt_mst.*", "vif", vif);
        uvm_config_db #(virtual ahb_interface.slave) :: set (this, "agt_slv.*", "vif", vif);

        // agent mode will always be UVM_ACTIVE in this project
        uvm_config_db #(uvm_active_passive_enum) :: set (this, "agt_mst", "agt_mode", UVM_ACTIVE);
        uvm_config_db #(uvm_active_passive_enum) :: set (this, "agt_slv", "agt_mode", UVM_ACTIVE);

        // Set fifo for ahb_slave_seq
        uvm_config_db #(uvm_tlm_analysis_fifo #(ahb_seq_item)) :: set (this, "*", "fifo", fifo);
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
