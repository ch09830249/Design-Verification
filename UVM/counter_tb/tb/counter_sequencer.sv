class counter_sequencer extends uvm_sequencer #(counter_seq_item);
    `uvm_component_utils(counter_sequencer)

    // p_sequencer target fields - virtual sequences cast to this
    logic [31:0] cfg_min;
    logic [31:0] cfg_max;
    int          reverse_cnt;   // tracks how many reverses have been applied

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        cfg_min     = 32'd0;
        cfg_max     = 32'd7;
        reverse_cnt = 0;
    endfunction
endclass : counter_sequencer
