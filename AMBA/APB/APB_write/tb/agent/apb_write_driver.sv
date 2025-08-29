class apb_write_driver extends uvm_driver #(apb_write_transaction);
  `uvm_component_utils(apb_write_driver)

  virtual apb_write_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_write_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "APB interface not found")
    end
  endfunction

  task run_phase(uvm_phase phase);
    apb_write_transaction tx;

    forever begin
      seq_item_port.get_next_item(tx);
  
      `uvm_info("apb_write_driver", "before write", UVM_LOW)
      tx.print(); 

      // APB idle -> setup -> enable
      @(posedge vif.PCLK);
      vif.PSEL    <= 1;
      vif.PWRITE  <= 1;
      vif.PENABLE <= 0;
      vif.PADDR   <= tx.addr;
      vif.PWDATA  <= tx.data;

      // Enable APB write
      @(posedge vif.PCLK);
      vif.PENABLE <= 1;

      // 等到 PREADY 舉起代表 module 已經收到資料
      wait (vif.PREADY == 1);

      // 回到 idle 狀態
      @(posedge vif.PCLK);
      vif.PSEL    <= 0;
      vif.PENABLE <= 0;
      vif.PWRITE  <= 0;
      vif.PADDR   <= 0;
      vif.PWDATA  <= 0;

      seq_item_port.item_done();
    end
  endtask
endclass
