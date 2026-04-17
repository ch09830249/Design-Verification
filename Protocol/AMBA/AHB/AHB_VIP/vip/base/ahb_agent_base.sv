`ifndef AHB_AGENT_BASE_SV
`define AHB_AGENT_BASE_SV

class ahb_agent_base extends uvm_agent;
    `uvm_component_utils(ahb_agent_base)

    ahb_driver_base                     drv;
    ahb_monitor_base                    mon;
    uvm_sequencer #(ahb_seq_item)       seqr;

    uvm_active_passive_enum             agt_mode;

    function new ( string name = "ahb_agent_base", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );
        super.build_phase(phase);

        if ( !uvm_config_db #(uvm_active_passive_enum) :: get (this, "", "agt_mode", agt_mode) )
            `uvm_fatal("NOAGTMODE", $sformatf("No agt_mode set for %s.agt_mode", get_full_name() ))

        uvm_config_db #(uvm_active_passive_enum) :: set (this, "*", "agt_mode", agt_mode);

        mon = ahb_monitor_base :: type_id :: create ("mon", this);

        if ( agt_mode == UVM_ACTIVE ) begin
            drv  = ahb_driver_base :: type_id :: create ("drv", this);
            seqr = uvm_sequencer #(ahb_seq_item) :: type_id :: create ("seqr", this);
        end
    endfunction

    function void connect_phase ( uvm_phase phase );
        super.connect_phase(phase);

        if ( agt_mode == UVM_ACTIVE )
            drv.seq_item_port.connect(seqr.seq_item_export);
    endfunction

endclass

`endif
