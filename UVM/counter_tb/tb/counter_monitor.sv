// =============================================================================
// File : counter_monitor.sv
// =============================================================================
class counter_monitor extends uvm_monitor;
    `uvm_component_utils(counter_monitor)

    virtual counter_if vif;   // plain virtual interface, no modport

    uvm_analysis_port #(counter_seq_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
        if (!uvm_config_db #(virtual counter_if)::get(this, "", "vif", vif))
            `uvm_fatal("NO_VIF", "counter_monitor: cannot get virtual interface")
    endfunction

    task run_phase(uvm_phase phase);
        counter_seq_item item;
        forever begin
            @(posedge vif.clk);
            #1; // small skew to sample after driver updates
            item           = counter_seq_item::type_id::create("mon_item");
            item.rst_n     = vif.rst_n;
            item.reverse   = vif.reverse;
            item.min_val   = vif.min_val;
            item.max_val   = vif.max_val;
            item.count     = vif.count;
            item.direction = vif.direction;
            ap.write(item);
        end
    endtask
endclass : counter_monitor
