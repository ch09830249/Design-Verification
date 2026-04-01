class apb_read_transaction extends uvm_sequence_item;
  rand bit [31:0] addr;
       bit [31:0] data;

  `uvm_object_utils_begin(apb_read_transaction)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "apb_read_transaction");
    super.new(name);
  endfunction
endclass
