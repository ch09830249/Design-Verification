// 支援 Master/Slave 模式
class axi_driver extends uvm_driver #(axi_txn);
    `uvm_component_utils(axi_driver)

    virtual axi_if vif;
    bit is_master;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
            `uvm_fatal("AXI_DRV", "virtual interface not found")
        if (!uvm_config_db#(bit)::get(this, "", "is_master", is_master))
            is_master = 1; // default: master
    endfunction

    task run_phase(uvm_phase phase);
        axi_txn tr;

        forever begin
            seq_item_port.get_next_item(tr);

            `uvm_info(get_type_name(), $sformatf("Get txn (is_write: %d)", tr.is_write), UVM_MEDIUM)
            tr.print();

            if (is_master) begin
                if (tr.is_write)
                    drive_write(tr);
                else
                    drive_read(tr);
            end else begin
                respond_slave(tr);
            end

            seq_item_port.item_done();
        end
    endtask

    task drive_write(axi_txn tr);
        // 等待 reset 解除
        while (!vif.ARESETn) @(posedge vif.ACLK);

        // =====================
        // Get address and control
        // =====================
        vif.AWID    <= tr.id;
        vif.AWADDR  <= tr.addr;
        vif.AWLEN   <= tr.burst_len;
        vif.AWSIZE  <= tr.burst_size;
        vif.AWBURST <= tr.burst_type;
        vif.AWLOCK  <= tr.lock;
        vif.AWQOS   <= tr.qos;
        
        // 發出寫入請求
        vif.AWVALID <= 1;
        vif.BREADY <= 1;    // 一發請求就等收 RESP
        
        // 先等下一個 posedge, 等待 AWREADY     
        do begin
            @(posedge vif.ACLK);
        end while(~vif.AWREADY);
        
        vif.AWVALID <= 0;
        // =====================
        // Get write data
        // =====================
        foreach (tr.data[i]) begin
            vif.WDATA  <= tr.data[i];
            vif.WSTRB  <= tr.wstrb;
            vif.WVALID <= 1;
            vif.WLAST  <= (i == tr.data.size()-1);

            // 先等下一個 posedge, 等待 ~WREADY
            do begin
                @(posedge vif.ACLK);
            end while(~vif.WREADY);
            vif.WVALID <= 0;
            vif.WLAST  <= 0;
        end

        // =====================
        // 等待 B channel 回應
        // =====================
        while (~vif.BVALID)
            @(posedge vif.ACLK);

        vif.BREADY  <= 0;
        vif.AWREADY <= 1;
    endtask

    task drive_read(axi_txn tr);
        int r_count = 0;
        // 等待 reset 解除
        while (!vif.ARESETn) @(posedge vif.ACLK);

        // =====================
        // Get address and control
        // =====================
        vif.ARID    <= tr.id;
        vif.ARADDR  <= tr.addr;
        vif.ARLEN   <= tr.burst_len;
        vif.ARSIZE  <= tr.burst_size;
        vif.ARBURST <= tr.burst_type;
        vif.ARLOCK  <= tr.lock;
        vif.ARQOS   <= tr.qos;

        // 發出讀取請求
        vif.ARVALID <= 1;

        // 先等下一個 posedge, 等待 ARREADY
        do begin
            @(posedge vif.ACLK);
        end while(~vif.ARREADY);

        vif.ARVALID <= 0;

        // 接收 R channel 資料
        while (r_count <= tr.burst_len) begin
            vif.RREADY <= 1;
            // 先等下一個 posedge, 等待 ~RVALID
            do begin
                @(posedge vif.ACLK);
            end while(~vif.RVALID);
            `uvm_info("AXI_DRV", $sformatf("Read data[%0d] = 0x%08x", r_count, vif.RDATA), UVM_LOW)
            vif.RREADY <= 0;
            r_count++;
            if (vif.RLAST) break;
        end
    endtask

    task respond_slave(axi_txn tr);
        // slave 被動等 master 發送訊號，這裡可視具體 DUT 模擬需要擴寫
        `uvm_info("AXI_DRV", "Slave response stub (implement as needed)", UVM_LOW)
    endtask
endclass
