class ahb_driver extends uvm_driver #(ahb_transaction);
  `uvm_component_utils(ahb_driver)

  virtual ahb_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual ahb_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "No virtual interface specified for ahb_driver")
  endfunction

  task run_phase(uvm_phase phase);
    ahb_transaction tx;
    forever begin
      seq_item_port.get_next_item(tx);

      // Setup phase
      vif.HSEL   <= 1;
      vif.HWRITE <= 1;
      vif.HADDR  <= tx.addr;
      vif.HWDATA <= tx.data;
      vif.HTRANS <= 2'b10; // NONSEQ

      // Wait for HREADY
      do @(posedge vif.HCLK); while (!vif.HREADYOUT);

      // Done
      vif.HSEL   <= 0;
      vif.HTRANS <= 2'b00;

      seq_item_port.item_done();
    end
  endtask
endclass
