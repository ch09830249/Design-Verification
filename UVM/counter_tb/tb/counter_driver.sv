// =============================================================================
// File : counter_driver.sv
// =============================================================================
class counter_driver extends uvm_driver #(counter_seq_item);
    `uvm_component_utils(counter_driver)

    virtual counter_if vif;   // plain virtual interface, no modport

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual counter_if)::get(this, "", "vif", vif))
            `uvm_fatal("NO_VIF", "counter_driver: cannot get virtual interface")
    endfunction

    task run_phase(uvm_phase phase);
        counter_seq_item item;
        vif.rst_n   <= 1'b0;
        vif.reverse <= 1'b0;
        vif.min_val <= 32'd0;
        vif.max_val <= 32'd7;
        repeat(3) @(posedge vif.clk);
        vif.rst_n <= 1'b1;
        @(posedge vif.clk);

        forever begin
            seq_item_port.get_next_item(item);
            drive_item(item);
            seq_item_port.item_done();
        end
    endtask

    task drive_item(counter_seq_item item);
        if (!item.rst_n) begin
            vif.rst_n <= 1'b0;
            @(posedge vif.clk);
            vif.rst_n <= 1'b1;
            @(posedge vif.clk);
        end else begin
            vif.min_val <= item.min_val;
            vif.max_val <= item.max_val;
            vif.reverse <= item.reverse;
            @(posedge vif.clk);
            vif.reverse <= 1'b0;
        end
    endtask
endclass : counter_driver
