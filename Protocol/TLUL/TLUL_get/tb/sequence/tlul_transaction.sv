class tlul_transaction extends uvm_sequence_item;
  rand bit [2:0]  opcode;
  rand bit [2:0]  param;
  rand bit [3:0]  size;
  rand bit [3:0]  mask;
  rand bit [31:0] address;
  rand bit [31:0] data;
  rand bit [2:0]  source;
  rand bit        is_get;    // Get or Put
  // Response fields
  bit [2:0]  resp_opcode;
  bit [2:0]  resp_param;
  bit [3:0]  resp_size;
  bit [31:0] resp_data;
  bit [2:0]  resp_source;
  bit [1:0]  resp_sink;

  `uvm_object_utils_begin(tlul_transaction)
        `uvm_field_int(opcode, UVM_ALL_ON)
        `uvm_field_int(param, UVM_ALL_ON)
        `uvm_field_int(size, UVM_ALL_ON)
        `uvm_field_int(mask, UVM_ALL_ON)
        `uvm_field_int(address, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(source, UVM_ALL_ON)
        `uvm_field_int(is_get, UVM_ALL_ON)
        `uvm_field_int(resp_opcode, UVM_ALL_ON)
        `uvm_field_int(resp_param, UVM_ALL_ON)
        `uvm_field_int(resp_size, UVM_ALL_ON)
        `uvm_field_int(resp_data, UVM_ALL_ON)
        `uvm_field_int(resp_source, UVM_ALL_ON)
        `uvm_field_int(resp_sink, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name="tlul_transaction");
    super.new(name);
  endfunction
endclass
