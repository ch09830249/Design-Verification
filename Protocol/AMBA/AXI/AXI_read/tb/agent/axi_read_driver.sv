class axi_read_driver extends uvm_driver #(axi_read_transaction);
  `uvm_component_utils(axi_read_driver)

  virtual axi_read_if vif;

  function new(string name = "axi_read_driver", uvm_component parent = null);  
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual axi_read_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal(get_type_name(), "Virtual interface not found!")
    end
  endfunction

  virtual task run_phase(uvm_phase phase);

    axi_read_transaction tr;
  
    forever begin
      seq_item_port.get_next_item(tr);

      `uvm_info(get_type_name(), "before read", UVM_MEDIUM)
      tr.print();

      // Read Address => assign ARADDR && ARVALID
      @(posedge vif.ACLK);
      vif.ARADDR  <= tr.araddr;                       // 塞入 read address 並且舉 ARVALID
      vif.ARVALID <= 1;

      // Wait for data & Response
      do @(posedge vif.ACLK); while (!vif.ARREADY);   // 等 module 收完 read address (ARREADY 被舉起)
      vif.ARVALID <= 0;                               // 將 ARVALID 放下並且舉起 RREADY 準備收 module 的 data
      vif.RREADY <= 1;

      // Read Data & RSP
      do @(posedge vif.ACLK); while (!vif.RVALID);    // 直到 RVALID 舉起代表 data 可以收了
      tr.rdata = vif.RDATA;                           // 收 DATA 和 RSP 之後 放下 RREADY
      tr.rresp = vif.RRESP;
      vif.RREADY <= 0;

      `uvm_info(get_type_name(), "after read", UVM_MEDIUM)
      tr.print();
      
      seq_item_port.item_done();
    end
  endtask
endclass

/*
 task drive_read(axi_read_xtn xtn);
    // AR channel
    axi_vif.arvalid <= 1;
    axi_vif.araddr  <= xtn.araddr;
    axi_vif.arid    <= xtn.arid;
    axi_vif.arlen   <= xtn.arlen;
    axi_vif.arsize  <= xtn.arsize;
    axi_vif.arburst <= xtn.arburst;

    wait (axi_vif.arready == 1);
    axi_vif.arvalid <= 0;

    // R channel - receive data
    for (int i = 0; i <= xtn.arlen; i++) begin
      wait (axi_vif.rvalid == 1);
      xtn.rdata[i] = axi_vif.rdata;
      axi_vif.rready <= 1;
      @(posedge axi_vif.clk);
      axi_vif.rready <= 0;
    end
  endtask
  */
