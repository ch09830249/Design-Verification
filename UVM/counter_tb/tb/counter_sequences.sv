// =============================================================================
// Desc : All sequences used in this testbench
// =============================================================================

// ---------------------------------------------------------------------------
// Base sequence - grants access to p_sequencer
// ---------------------------------------------------------------------------
class counter_base_seq extends uvm_sequence #(counter_seq_item);
    `uvm_object_utils(counter_base_seq)
    `uvm_declare_p_sequencer(counter_sequencer)  //  p_sequencer

    function new(string name = "counter_base_seq");
        super.new(name);
    endfunction
endclass : counter_base_seq

// ---------------------------------------------------------------------------
// Reset sequence
// ---------------------------------------------------------------------------
class counter_reset_seq extends counter_base_seq;
    `uvm_object_utils(counter_reset_seq)

    function new(string name = "counter_reset_seq");
        super.new(name);
    endfunction

    task body();
        counter_seq_item item;
        `uvm_create(item)
        item.rst_n   = 1'b0;
        item.reverse = 1'b0;
        item.min_val = p_sequencer.cfg_min;
        item.max_val = p_sequencer.cfg_max;
        `uvm_send(item)
        `uvm_info("RESET_SEQ", "Reset applied", UVM_MEDIUM)
    endtask
endclass : counter_reset_seq

// ---------------------------------------------------------------------------
// Count-up sequence: run N cycles without reversing
// ---------------------------------------------------------------------------
class counter_count_seq extends counter_base_seq;
    `uvm_object_utils(counter_count_seq)

    int num_cycles = 20;

    function new(string name = "counter_count_seq");
        super.new(name);
    endfunction

    task body();
        counter_seq_item item;
        repeat(num_cycles) begin
            `uvm_create(item)
            item.rst_n   = 1'b1;
            item.reverse = 1'b0;
            item.min_val = p_sequencer.cfg_min;
            item.max_val = p_sequencer.cfg_max;
            `uvm_send(item)
        end
        `uvm_info("COUNT_SEQ",
            $sformatf("Ran %0d cycles (min=%0d max=%0d)",
                num_cycles, p_sequencer.cfg_min, p_sequencer.cfg_max),
            UVM_MEDIUM)
    endtask
endclass : counter_count_seq

// ---------------------------------------------------------------------------
// Reverse sequence: issue a single reverse pulse then wait N cycles
// ---------------------------------------------------------------------------
class counter_reverse_seq extends counter_base_seq;
    `uvm_object_utils(counter_reverse_seq)

    int post_cycles = 10;

    function new(string name = "counter_reverse_seq");
        super.new(name);
    endfunction

    task body();
        counter_seq_item item;
        // One-cycle reverse pulse
        `uvm_create(item)
        item.rst_n   = 1'b1;
        item.reverse = 1'b1;
        item.min_val = p_sequencer.cfg_min;
        item.max_val = p_sequencer.cfg_max;
        `uvm_send(item)
        p_sequencer.reverse_cnt++;
        `uvm_info("REVERSE_SEQ",
            $sformatf("Reverse #%0d issued", p_sequencer.reverse_cnt),
            UVM_MEDIUM)
        // Post-reverse cycles
        repeat(post_cycles) begin
            `uvm_create(item)
            item.rst_n   = 1'b1;
            item.reverse = 1'b0;
            item.min_val = p_sequencer.cfg_min;
            item.max_val = p_sequencer.cfg_max;
            `uvm_send(item)
        end
    endtask
endclass : counter_reverse_seq

// ---------------------------------------------------------------------------
// Config-change sequence: change min/max mid-run
// ---------------------------------------------------------------------------
class counter_cfg_seq extends counter_base_seq;
    `uvm_object_utils(counter_cfg_seq)

    logic [31:0] new_min;
    logic [31:0] new_max;
    int          run_cycles = 15;

    function new(string name = "counter_cfg_seq");
        super.new(name);
    endfunction

    task body();
        counter_seq_item item;
        p_sequencer.cfg_min = new_min;
        p_sequencer.cfg_max = new_max;
        `uvm_info("CFG_SEQ",
            $sformatf("Config changed -> min=%0d max=%0d",
                new_min, new_max),
            UVM_MEDIUM)
        repeat(run_cycles) begin
            `uvm_create(item)
            item.rst_n   = 1'b1;
            item.reverse = 1'b0;
            item.min_val = p_sequencer.cfg_min;
            item.max_val = p_sequencer.cfg_max;
            `uvm_send(item)
        end
    endtask
endclass : counter_cfg_seq

// ---------------------------------------------------------------------------
// Boundary-stress sequence: push counter right to boundaries
// ---------------------------------------------------------------------------
class counter_boundary_seq extends counter_base_seq;
    `uvm_object_utils(counter_boundary_seq)

    function new(string name = "counter_boundary_seq");
        super.new(name);
    endfunction

    task body();
        counter_seq_item item;
        // Run enough cycles to cross both boundaries multiple times
        int cycles = (p_sequencer.cfg_max - p_sequencer.cfg_min + 1) * 4;
        repeat(cycles) begin
            `uvm_create(item)
            item.rst_n   = 1'b1;
            item.reverse = 1'b0;
            item.min_val = p_sequencer.cfg_min;
            item.max_val = p_sequencer.cfg_max;
            `uvm_send(item)
        end
        `uvm_info("BOUNDARY_SEQ",
            $sformatf("Boundary stress done (%0d cycles)", cycles),
            UVM_MEDIUM)
    endtask
endclass : counter_boundary_seq
