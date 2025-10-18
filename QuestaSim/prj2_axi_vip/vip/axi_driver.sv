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
        // 寫地址通道
        vif.AWID    <= tr.id;
        vif.AWADDR  <= tr.addr;
        vif.AWLEN   <= tr.burst_len;
        vif.AWSIZE  <= tr.burst_size;
        vif.AWBURST <= tr.burst_type;
        vif.AWLOCK  <= tr.lock;
        vif.AWQOS   <= tr.qos;
        vif.AWVALID <= 1;

        wait (vif.AWREADY);
        vif.AWVALID <= 0;

        // 寫資料通道
        foreach (tr.data[i]) begin
            vif.WDATA  <= tr.data[i];
            vif.WSTRB  <= '1;
            vif.WLAST  <= (i == tr.data.size()-1);
            vif.WVALID <= 1;
            wait (vif.WREADY);
            vif.WVALID <= 0;
        end

        // 等待 B channel response
        vif.BREADY <= 1;
        wait (vif.BVALID);
        vif.BREADY <= 0;
    endtask

    task drive_read(axi_txn tr);
        // 發出讀取請求
        vif.ARID    <= tr.id;
        vif.ARADDR  <= tr.addr;
        vif.ARLEN   <= tr.burst_len;
        vif.ARSIZE  <= tr.burst_size;
        vif.ARBURST <= tr.burst_type;
        vif.ARLOCK  <= tr.lock;
        vif.ARQOS   <= tr.qos;
        vif.ARVALID <= 1;

        wait (vif.ARREADY);
        vif.ARVALID <= 0;

        // 接收 R channel 資料
        int r_count = 0;
        while (r_count <= tr.burst_len) begin
            vif.RREADY <= 1;
            wait (vif.RVALID);
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
