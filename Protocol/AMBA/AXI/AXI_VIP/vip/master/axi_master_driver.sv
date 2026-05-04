`ifndef AXI_MASTER_DRIVER_SV
`define AXI_MASTER_DRIVER_SV

class axi_master_driver extends axi_driver_base;
    `uvm_component_utils(axi_master_driver)

    axi_seq_item    aw_queue[$];
    axi_seq_item    w_queue[$];
    axi_seq_item    ar_queue[$];

    function new(string name = "axi_master_driver", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        reset_signal();
        @(posedge vif.ARESETn);
        @(posedge vif.ACLK);
        fork
            monitor_reset();
            insert_cmd_queue();
            drive_aw_channel();
            drive_w_channel();
            drive_b_channel();
            drive_ar_channel();
            drive_r_channel();
        join
    endtask

    task insert_cmd_queue();
        forever begin
            seq_item_port.get_next_item(txn);
            if (txn.write) begin
                aw_queue.push_back(txn);
            end else
                ar_queue.push_back(txn);
            seq_item_port.item_done();
        end
    endtask

    task drive_aw_channel();
        axi_seq_item cur;
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.AWVALID <= 0;
            end else begin
                if (aw_queue.size() > 0 && !vif.AWVALID) begin
                    cur = aw_queue.pop_front();
                    vif.AWID    <= cur.id;
                    vif.AWADDR  <= cur.addr;
                    vif.AWLEN   <= cur.len;
                    vif.AWSIZE  <= cur.size;
                    vif.AWBURST <= cur.burst;
                    vif.AWVALID <= 1;
                    w_queue.push_back(cur);
                end else if (vif.AWVALID && vif.AWREADY) begin
                    vif.AWVALID <= 0;
                end
            end
        end
    endtask

    task drive_w_channel();
        forever begin
            axi_seq_item cur;

            wait(w_queue.size() > 0);
            cur = w_queue.pop_front();

            for (int beat = 0; beat <= cur.len; beat++) begin
                @(posedge vif.ACLK);
                if (!vif.ARESETn) break;

                vif.WDATA  <= cur.wdata[beat];
                vif.WSTRB  <= cur.wstrb[beat];
                vif.WLAST  <= (beat == cur.len);
                vif.WVALID <= 1;

                while (!vif.WREADY) begin
                    @(posedge vif.ACLK);
                    if (!vif.ARESETn) break;
                end

                if (!vif.ARESETn) break;
            end

            vif.WVALID <= 0;
            vif.WLAST  <= 0;
        end
    endtask

    task drive_b_channel();
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.BREADY <= 0;
            end else begin
                vif.BREADY <= 1;
                if (vif.BVALID) begin
                    if (vif.BRESP !== `BRESP_OKAY)
                        `uvm_error("MSTDRV", $sformatf("BRESP error: 0x%h", vif.BRESP))
                end
            end
        end
    endtask

    task drive_ar_channel();
        axi_seq_item cur;
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.ARVALID <= 0;
            end else begin
                if (ar_queue.size() > 0 && !vif.ARVALID) begin
                    cur = ar_queue.pop_front();
                    vif.ARID    <= cur.id;
                    vif.ARADDR  <= cur.addr;
                    vif.ARLEN   <= cur.len;
                    vif.ARSIZE  <= cur.size;
                    vif.ARBURST <= cur.burst;
                    vif.ARVALID <= 1;
                end else if (vif.ARVALID && vif.ARREADY) begin
                    vif.ARVALID <= 0;
                end
            end
        end
    endtask

    task drive_r_channel();
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.RREADY <= 0;
            end else begin
                vif.RREADY <= 1;
                if (vif.RVALID) begin
                    if (vif.RRESP !== `RRESP_OKAY)
                        `uvm_error("MSTDRV", $sformatf("RRESP error: beat RRESP=0x%h", vif.RRESP))
                end
            end
        end
    endtask

    task reset_signal();
        vif.AWID    <= '0;
        vif.AWADDR  <= '0;
        vif.AWLEN   <= '0;
        vif.AWSIZE  <= '0;
        vif.AWBURST <= '0;
        vif.AWVALID <= '0;
        vif.WDATA   <= '0;
        vif.WSTRB   <= '0;
        vif.WLAST   <= '0;
        vif.WVALID  <= '0;
        vif.BREADY  <= '0;
        vif.ARID    <= '0;
        vif.ARADDR  <= '0;
        vif.ARLEN   <= '0;
        vif.ARSIZE  <= '0;
        vif.ARBURST <= '0;
        vif.ARVALID <= '0;
        vif.RREADY  <= '0;
    endtask

    task monitor_reset();
        forever begin
            @(negedge vif.ARESETn);
            flush_queues();
            reset_signal();
            `uvm_info("MSTDRV", "Reset asserted: queues flushed", UVM_MEDIUM)
            @(posedge vif.ARESETn);
            @(posedge vif.ACLK);
            `uvm_info("MSTDRV", "Reset deasserted: driver resumed", UVM_MEDIUM)
        end
    endtask

    task flush_queues();
        aw_queue.delete();
        w_queue.delete();
        ar_queue.delete();
    endtask

endclass

`endif
