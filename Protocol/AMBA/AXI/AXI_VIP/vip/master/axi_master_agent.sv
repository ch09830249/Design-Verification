`ifndef AXI_MASTER_AGENT_SV
`define AXI_MASTER_AGENT_SV

class axi_master_agent extends axi_agent_base;
    `uvm_component_utils(axi_master_agent)

    function new(string name = "axi_master_agent", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);

        factory.set_inst_override_by_type(
            axi_driver_base::get_type(),
            axi_master_driver::get_type(),
            "*agt_mst.*"
        );

        factory.set_inst_override_by_type(
            axi_monitor_base::get_type(),
            axi_master_monitor::get_type(),
            "*agt_mst.*"
        );

        super.build_phase(phase);
    endfunction

endclass

`endif
