class axi_read_sequence extends uvm_sequence #(axi_read_transaction);
  `uvm_object_utils(axi_read_sequence)

  function new(string name = "axi_read_sequence");
    super.new(name);
  endfunction

  virtual task body();
    axi_read_transaction tr;
    `uvm_info(get_type_name(), "Starting AXI read sequence", UVM_MEDIUM)
    // 送 3 比 read transaction (Read address 隨機)
    for (int i = 0; i < 3; i++) begin
      tr = axi_read_transaction::type_id::create("tr");
      assert(tr.randomize());
      start_item(tr);
      finish_item(tr);
    end

    `uvm_info(get_type_name(), $sformatf("Read transaction sent: addr=0x%08h", tr.araddr), UVM_MEDIUM)
  endtask
endclass
