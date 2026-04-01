class axi_write_sequence extends uvm_sequence #(axi_write_transaction);
  `uvm_object_utils(axi_write_sequence)

  function new(string name = "axi_write_sequence");
    super.new(name);
  endfunction

  virtual task body();
    axi_write_transaction tr;
    for (int i = 0; i < 3; i++) begin       // 發送 3 筆 write
      tr = axi_write_transaction::type_id::create("tr");
      assert(tr.randomize());
      tr.print();
      start_item(tr);
      finish_item(tr);
    end
  endtask
endclass
