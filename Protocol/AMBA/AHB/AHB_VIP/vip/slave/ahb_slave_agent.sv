`ifndef AHB_SLAVE_AGENT_SV
`define AHB_SLAVE_AGENT_SV

class ahb_slave_agent extends ahb_agent_base;
    `uvm_component_utils(ahb_slave_agent)

    function new ( string name = "ahb_slave_agent", uvm_component parent );
        super.new(name, parent);
    endfunction

    function void build_phase ( uvm_phase phase );

        factory.set_inst_override_by_type (
            ahb_driver_base::get_type(),
            ahb_slave_driver::get_type(),
            "*agt_slv.*"
        );

        factory.set_inst_override_by_type (
            ahb_monitor_base::get_type(),
            ahb_slave_monitor::get_type(),
            "*agt_slv.*"
        );

        super.build_phase(phase);
    endfunction
endclass

`endif
