`ifndef APB_MASTER_AGENT_SV
`define APB_MASTER_AGENT_SV

class ahb_master_agent extends ahb_agent_base;
    `uvm_component_utils(apb_master_agent)

    function new ( string name = "apb_master_agent", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );

        factory.set_inst_override_by_type (
            apb_driver_base::get_type(),
            apb_master_driver::get_type(),
            "*agt_mst.*"
        );

        factory.set_inst_override_by_type (
            apb_monitor_base::get_type(),
            apb_master_monitor::get_type(),
            "*agt_mst.*"
        );

        super.build_phase(phase);
    endfunction
endclass

`endif
