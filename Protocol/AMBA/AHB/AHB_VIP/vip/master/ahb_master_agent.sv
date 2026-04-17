`ifndef AHB_MASTER_AGENT_SV
`define AHB_MASTER_AGENT_SV

class ahb_master_agent extends ahb_agent_base;
    `uvm_component_utils(ahb_master_agent)

    function new ( string name = "ahb_master_agent", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );

        factory.set_inst_override_by_type (
            ahb_driver_base::get_type(),
            ahb_master_driver::get_type(),
            "*agt_mst.*"
        );

        factory.set_inst_override_by_type (
            ahb_monitor_base::get_type(),
            ahb_master_monitor::get_type(),
            "*agt_mst.*"
        );

        super.build_phase(phase);
    endfunction
endclass

`endif
