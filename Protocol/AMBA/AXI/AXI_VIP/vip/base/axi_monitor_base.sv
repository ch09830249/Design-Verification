`ifndef AXI_MONITOR_BASE_SV
`define AXI_MONITOR_BASE_SV

class axi_monitor_base extends uvm_monitor;
    `uvm_component_utils(axi_monitor_base)

    virtual axi_interface               vif;
    axi_seq_item                        txn;
    uvm_active_passive_enum             agt_mode;
    uvm_analysis_port #(axi_seq_item)   port;

    function new(string name = "axi_monitor_base", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        port = new("port", this);

        if (!uvm_config_db #(virtual axi_interface)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", $sformatf("No interface set for %s.vif", get_full_name()))

        if (!uvm_config_db #(uvm_active_passive_enum)::get(this, "", "agt_mode", agt_mode))
            `uvm_fatal("NOAGTMODE", $sformatf("No agt_mode set for %s.agt_mode", get_full_name()))
    endfunction

endclass

`endif
