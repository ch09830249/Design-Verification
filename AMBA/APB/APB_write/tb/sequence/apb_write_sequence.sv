class apb_write_sequence extends uvm_sequence #(apb_write_transaction);
  `uvm_object_utils(apb_write_sequence)

  function new(string name = "apb_write_sequence");
    super.new(name);
  endfunction

  task body();
    apb_write_transaction tx;
    repeat (3) begin        // 發 3 筆 APB write
      tx = apb_write_transaction::type_id::create("tx");
      tx.randomize() with {
        addr inside {[32'h0000_0000 : 32'h0000_00FF]};    // 現在 addr 範圍限制 (因為 module 內的 mem 就只有 0 ~ 255)
      };
      start_item(tx);
      finish_item(tx);
    end
  endtask
endclass
