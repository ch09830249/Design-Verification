class axi_read_transaction extends uvm_sequence_item;
  rand bit [31:0] araddr;
  bit [31:0] rdata;
  bit [1:0]  rresp;

  `uvm_object_utils_begin(axi_read_transaction)
    `uvm_field_int(araddr, UVM_ALL_ON)
    `uvm_field_int(rdata, UVM_ALL_ON)
    `uvm_field_int(rresp, UVM_ALL_ON)
  `uvm_object_utils_end

  function new(string name = "axi_read_transaction");
    super.new(name);
  endfunction
endclass
