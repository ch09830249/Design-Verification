class ahb_write_driver extends uvm_driver #(ahb_transaction);
  `uvm_component_utils(ahb_write_driver)

  virtual ahb_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not set")
  endfunction

  task run_phase(uvm_phase phase);
  forever begin
    ahb_transaction tr;
    seq_item_port.get_next_item(tr);
    `uvm_info(get_type_name(), "Write data transaction", UVM_MEDIUM)
    tr.print();
    
    // Drive write address phase
    vif.cb.HADDR  <= tr.addr;
    vif.cb.HTRANS <= 2'b10;   // NONSEQ
    vif.cb.HWRITE <= 1'b1;
    vif.cb.HSIZE  <= tr.size;

    // Write data
    @(posedge vif.HCLK iff vif.HREADY);
    // Drive write data phase
    vif.cb.HWDATA <= tr.data;

    @(posedge vif.HCLK iff vif.HREADY);

    // Done
    seq_item_port.item_done();
  end
endtask

endclass
