class ahb_seq_item extends uvm_sequence_item;
  rand bit [31:0] addr;
  rand bit [31:0] data;

  `uvm_object_utils(ahb_seq_item)

  function new(string name = "ahb_seq_item");
    super.new(name);
  endfunction
endclass
