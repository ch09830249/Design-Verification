class counter_seq_item extends uvm_sequence_item;

    rand logic        reverse;
    rand logic [31:0] min_val;
    rand logic [31:0] max_val;
         logic        rst_n;

    // Response fields (sampled by monitor)
    logic [31:0] count;
    logic        direction;

    `uvm_object_utils_begin(counter_seq_item)
        `uvm_field_int(reverse,   UVM_ALL_ON)
        `uvm_field_int(min_val,   UVM_ALL_ON)
        `uvm_field_int(max_val,   UVM_ALL_ON)
        `uvm_field_int(count,     UVM_ALL_ON)
        `uvm_field_int(direction, UVM_ALL_ON)
        `uvm_field_int(rst_n,     UVM_ALL_ON)
    `uvm_object_utils_end

    // Constraints
    constraint c_range  { max_val > min_val; }
    constraint c_spread { (max_val - min_val) inside {[3:15]}; }
    constraint c_min    { min_val inside {[0:20]}; }

    function new(string name = "counter_seq_item");
        super.new(name);
    endfunction
endclass : counter_seq_item
