class apb_read_driver extends uvm_driver #(apb_read_transaction);
  `uvm_component_utils(apb_read_driver)

  virtual apb_read_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_read_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "No APB read interface found")
  endfunction

  task run_phase(uvm_phase phase);
    apb_read_transaction tx;
    forever begin
      seq_item_port.get_next_item(tx);

      `uvm_info("apb_read_driver", "before read", UVM_LOW)
      tx.print();
      
      // APB idle -> setup -> enable
      @(posedge vif.PCLK);
      vif.PADDR   <= tx.addr;
      vif.PWRITE  <= 0;
      vif.PSEL    <= 1;
      vif.PENABLE <= 0;

      // Trigger APB read
      @(posedge vif.PCLK);
      vif.PENABLE <= 1;

      // Wait for PREADY
      wait (vif.PREADY == 1);

      // Get read data
      @(posedge vif.PCLK);
      tx.data = vif.PRDATA;

      // Restore PSEL && PENABLE
      vif.PSEL    <= 0;
      vif.PENABLE <= 0;

      `uvm_info("apb_read_driver", "after read", UVM_LOW)
      tx.print();

      seq_item_port.item_done();
    end
  endtask
endclass
