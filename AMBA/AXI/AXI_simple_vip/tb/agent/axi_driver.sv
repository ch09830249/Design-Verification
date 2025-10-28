class axi_write_driver extends uvm_driver #(axi_write_transaction);
  `uvm_component_utils(axi_write_driver)

  virtual axi_write_if vif;

  function new(string name = "axi_write_driver", uvm_component parent = null); 
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    if (!uvm_config_db#(virtual axi_write_if)::get(this, "", "vif", vif))   // 取得從 top 傳來的 virtual interface
      `uvm_fatal("DRV", "No virtual interface bound to driver");
  endfunction

  virtual task run_phase(uvm_phase phase);
    axi_write_transaction tr;

    forever begin
      seq_item_port.get_next_item(tr);

      // Write Address => assign AWADDR && AWVALID
      // @(posedge vif.ACLK);
      vif.AWADDR  <= tr.addr;                         // 塞 tr 的 write address
      vif.AWVALID <= 1;                               // 舉 AWVALID 表示 module 可以取 write address

      // Write data
      wait (vif.AWREADY == 1);                        // 直到 AWREADY 為 1
      vif.AWVALID <= 0;                               // 將 AWVALID 放下, 準備塞 data
      vif.WDATA  <= tr.data;                          // 塞 tr 的 write data
      vif.WVALID <= 1;                                // 舉 WVALID 表示可以取 write data
      
      // Write data done
      wait (vif.WREADY == 1);                         // 直到 WREADY 為 1
      vif.WVALID <= 0;                                // 將 WVALID 放下, 準備等待 write data 有沒有成功

      // Wait for Response
      wait (vif.BVALID == 1);                         // 直到 BVALID 為 1
      `uvm_info("DRV", $sformatf("BRESP: %0d", vif.BRESP), UVM_LOW);
      vif.BREADY <= 1;                                // 看完狀態把 BREADY 舉起代表我看完了

      // Reset BREADY
      @(posedge vif.ACLK);
      vif.BREADY <= 0;                                // 等一個 clk 之後回復 BREADY 狀態

      seq_item_port.item_done();
    end
  endtask
endclass
