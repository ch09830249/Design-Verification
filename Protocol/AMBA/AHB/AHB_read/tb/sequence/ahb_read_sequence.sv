class ahb_read_sequence extends uvm_sequence #(ahb_transaction);
  `uvm_object_utils(ahb_read_sequence)

  function new(string name = "ahb_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    ahb_transaction tr;
    repeat(4) begin
      tr = ahb_transaction::type_id::create("tr");
      tr.randomize() with { 
        tr.addr[15:0] == 16'h0000; 
        tr.size == 3'b010; // Word aligned
        tr.data == 32'h0;
      };
      start_item(tr);
      finish_item(tr);
      `uvm_info("AHB_SEQ", $sformatf("Read Data: 0x%08X", tr.data), UVM_MEDIUM)
    end
  endtask
endclass
