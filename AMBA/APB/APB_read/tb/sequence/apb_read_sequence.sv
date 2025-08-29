class apb_read_sequence extends uvm_sequence #(apb_read_transaction);
  `uvm_object_utils(apb_read_sequence)

  function new(string name = "apb_read_sequence");
    super.new(name);
  endfunction

  task body();
    apb_read_transaction tx;
    for(int i = 0; i < 4; i++) begin                    // 發 4 筆 APB write
      tx = apb_read_transaction::type_id::create("tx");
      tx.addr = 32'h1000 + i * 4;                       // addr: 32'h1000, 32'h1004, 32'h1008, 32'h100C...
      tx.data = 0;
      start_item(tx);
      finish_item(tx);
    end
  endtask
endclass
