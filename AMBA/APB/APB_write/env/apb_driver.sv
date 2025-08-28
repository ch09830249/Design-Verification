class apb_driver extends uvm_driver #(apb_transaction);
  `uvm_component_utils(apb_driver)

  virtual apb_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "APB interface not found")
    end
  endfunction

  task run_phase(uvm_phase phase);
    apb_transaction tx;

    forever begin
      seq_item_port.get_next_item(tx);

      // Drive APB write
      vif.PSEL    <= 1;
      vif.PWRITE  <= 1;
      vif.PADDR   <= tx.addr;
      vif.PWDATA  <= tx.data;
      vif.PENABLE <= 0;
      @(posedge vif.PCLK);

      vif.PENABLE <= 1;
      @(posedge vif.PCLK);

      wait (vif.PREADY == 1);
      vif.PSEL    <= 0;
      vif.PENABLE <= 0;

      seq_item_port.item_done();
    end
  endtask
endclass
