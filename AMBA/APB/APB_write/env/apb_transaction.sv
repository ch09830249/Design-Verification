class apb_transaction extends uvm_sequence_item;
  rand bit [31:0] addr;
  rand bit [31:0] data;

  `uvm_object_utils(apb_transaction)

  function new(string name = "apb_transaction");
    super.new(name);
  endfunction

  function void do_print(uvm_printer printer);
    super.do_print(printer);
    printer.print_field_int("addr", addr, 32);
    printer.print_field_int("data", data, 32);
  endfunction
endclass
