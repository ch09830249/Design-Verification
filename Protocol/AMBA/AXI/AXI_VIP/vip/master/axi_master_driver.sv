`ifndef AXI_MASTER_DRIVER_SV
`define AXI_MASTER_DRIVER_SV

class axi_master_driver extends axi_driver_base;
    `uvm_component_utils(axi_master_driver)

    axi_seq_item    aw_queue[$];    // AW channel pending
    axi_seq_item    w_queue[$];     // W  channel pending
    axi_seq_item    ar_queue[$];    // AR channel pending

    function new(string name = "axi_master_driver", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        reset_signal();
        @(posedge vif.ARESETn);    // 等 reset 結束
        @(vif.master_cb);    // wait one cycle after reset
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

    // ----------------------------------------------------------------
    // Get txn from sequencer, dispatch to AW or AR queue
    // ----------------------------------------------------------------
    task insert_cmd_queue();
        forever begin
            seq_item_port.get_next_item(txn);
            `uvm_info("MSTDRV", "Got txn from sequencer", UVM_LOW)  // ← 加這行
            txn.print();

            if (txn.write)
                aw_queue.push_back(txn);
            else
                ar_queue.push_back(txn);

            seq_item_port.item_done();
        end
    endtask

    // ----------------------------------------------------------------
    // AW channel
    // ----------------------------------------------------------------
    task drive_aw_channel();
        axi_seq_item cur;
        forever begin
            @(vif.master_cb);
            if (!vif.ARESETn) begin
                vif.master_cb.AWVALID <= 0;
            end else begin
                `uvm_info("MSTDRV", $sformatf("aw_queue.size=%0d AWVALID=%0b", aw_queue.size(), vif.AWVALID), UVM_LOW)
                if (aw_queue.size() > 0 && !vif.AWVALID) begin
                    `uvm_info("MSTDRV", "Driving AW channel", UVM_LOW)
                    cur = aw_queue.pop_front();
                    vif.master_cb.AWID    <= cur.id;
                    vif.master_cb.AWADDR  <= cur.addr;
                    vif.master_cb.AWLEN   <= cur.len;
                    vif.master_cb.AWSIZE  <= cur.size;
                    vif.master_cb.AWBURST <= cur.burst;
                    vif.master_cb.AWVALID <= 1;
                    w_queue.push_back(cur);    // mirror to W queue
                end else if (vif.AWVALID && vif.AWREADY) begin
                    vif.master_cb.AWVALID <= 0;
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // W channel — drive wdata[]/wstrb[] beat by beat
    // ----------------------------------------------------------------
    task drive_w_channel();
        forever begin
            axi_seq_item cur;

            wait(w_queue.size() > 0);
            cur = w_queue.pop_front();

            for (int beat = 0; beat <= cur.len; beat++) begin
                @(vif.master_cb);
                if (!vif.ARESETn) break;

                vif.master_cb.WDATA  <= cur.wdata[beat];
                vif.master_cb.WSTRB  <= cur.wstrb[beat];
                vif.master_cb.WLAST  <= (beat == cur.len);
                vif.master_cb.WVALID <= 1;

                while (!vif.WREADY) begin
                    @(vif.master_cb);
                    if (!vif.ARESETn) break;
                end

                // For previous while loop
                if (!vif.ARESETn) break;
            end

            // Clear WVALID and WLAST
            vif.master_cb.WVALID <= 0;
            vif.master_cb.WLAST  <= 0;
        end
    endtask

    // ----------------------------------------------------------------
    // B channel — accept write response
    // ----------------------------------------------------------------
    task drive_b_channel();
        forever begin
            @(vif.master_cb);
            if (!vif.ARESETn) begin
                vif.master_cb.BREADY <= 0;
            end else begin
                vif.master_cb.BREADY <= 1;    // always ready to accept response
                if (vif.BVALID) begin
                    if (vif.BRESP !== `BRESP_OKAY)
                        `uvm_error("MSTDRV", $sformatf("BRESP error: 0x%h", vif.BRESP))
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // AR channel
    // ----------------------------------------------------------------
    task drive_ar_channel();
        axi_seq_item cur;
        forever begin
            @(vif.master_cb);
            if (!vif.ARESETn) begin
                vif.master_cb.ARVALID <= 0;
            end else begin
                if (ar_queue.size() > 0 && !vif.ARVALID) begin
                    cur = ar_queue.pop_front();
                    vif.master_cb.ARID    <= cur.id;
                    vif.master_cb.ARADDR  <= cur.addr;
                    vif.master_cb.ARLEN   <= cur.len;
                    vif.master_cb.ARSIZE  <= cur.size;
                    vif.master_cb.ARBURST <= cur.burst;
                    vif.master_cb.ARVALID <= 1;
                end else if (vif.ARVALID && vif.ARREADY) begin
                    vif.master_cb.ARVALID <= 0;
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // R channel — accept read data beat by beat
    // ----------------------------------------------------------------
    task drive_r_channel();
        forever begin
            @(vif.master_cb);
            if (!vif.ARESETn) begin
                vif.master_cb.RREADY <= 0;
            end else begin
                vif.master_cb.RREADY <= 1;    // always ready to accept data
                if (vif.RVALID) begin
                    if (vif.RRESP !== `RRESP_OKAY)
                        `uvm_error("MSTDRV", $sformatf("RRESP error: beat RRESP=0x%h", vif.RRESP))
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // Reset
    // ----------------------------------------------------------------
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

    // ----------------------------------------------------------------
    // Reset monitor — 偵測 reset 發生時清空 queues
    // ----------------------------------------------------------------
    task monitor_reset();
        forever begin
            @(negedge vif.ARESETn);                          // reset 拉低
            flush_queues();
            reset_signal();
            `uvm_info("MSTDRV", "Reset asserted: queues flushed", UVM_MEDIUM)

            @(posedge vif.ARESETn);                          // reset 釋放
            @(vif.master_cb);                        // 再等一拍穩定
            `uvm_info("MSTDRV", "Reset deasserted: driver resumed", UVM_MEDIUM)
        end
    endtask

    // ----------------------------------------------------------------
    // Flush all pending queues
    // ----------------------------------------------------------------
    task flush_queues();
        aw_queue.delete();
        w_queue.delete();
        ar_queue.delete();
    endtask

endclass

`endif
