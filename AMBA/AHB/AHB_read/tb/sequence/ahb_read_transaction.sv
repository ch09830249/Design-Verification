class ahb_transaction extends uvm_sequence_item;
  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit [2:0] size;

  `uvm_object_utils_begin(ahb_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(size, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "ahb_transaction");
    super.new(name);
  endfunction
endclass
