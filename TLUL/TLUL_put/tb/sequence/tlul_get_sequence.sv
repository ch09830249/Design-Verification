class tlul_get_sequence extends uvm_sequence #(tlul_transaction);
  `uvm_object_utils(tlul_get_sequence)

  rand bit [31:0] address;
  rand bit [31:0] data;
  rand bit        is_get;

  function new(string name="tlul_get_sequence");
    super.new(name);
  endfunction

  virtual task body();
    tlul_transaction tr;
    repeat(5) begin
      tr = tlul_transaction::type_id::create("tr");
      // address 隨機產生
      assert(tr.randomize() with {
        is_get == 1;                        // 固定下 Get
        opcode == 4;                        // 4 = Get, 0 = Put
        size   == 2;                        // 4‑byte (這裡都固定 32 bits)
        data   == 32'h0;                    // is_get ? 32'h0 : data;
        param  == 0;
        mask inside {[4'h0 : 4'hF]};        // 可以決定哪個 byte 才有效
      });
      start_item(tr);
      finish_item(tr);
    end
  endtask
endclass
