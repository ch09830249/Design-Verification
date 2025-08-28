class apb_write_sequence extends uvm_sequence #(apb_transaction);
  `uvm_object_utils(apb_write_sequence)

  function new(string name = "apb_write_sequence");
    super.new(name);
  endfunction

  task body();
    apb_transaction tx = apb_transaction::type_id::create("tx");
    foreach (int i [0:4]) begin
      tx.randomize() with {
        addr inside {[32'h0000_0000 : 32'h0000_00FF]};
      };
      start_item(tx);
      finish_item(tx);
    end
  endtask
endclass
