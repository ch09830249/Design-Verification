class tlul_put_sequence extends uvm_sequence #(tlul_transaction);
  `uvm_object_utils(tlul_put_sequence)

  function new(string name="tlul_put_sequence");
    super.new(name);
  endfunction

  virtual task body();
    tlul_transaction tr;

    repeat (5) begin
      tr = tlul_transaction::type_id::create("tr");

      // 隨機化 transaction
      assert(tr.randomize() with {
        is_get == 0;                                  // 表示這是 Put 操作
        opcode inside {[3'b000 : 3'b001]};             // 000 = PutFull, 001 = PutPartial
        size == 4;                                    // 4 bytes (word)
        param == 0;
        mask inside {4'hF, 4'h1, 4'h3, 4'hC};         // 模擬不同 byte mask
        data inside {[32'h00000000 : 32'hFFFFFFFF]};  // 寫入資料
      });

      start_item(tr);
      finish_item(tr);
    end
  endtask
endclass

