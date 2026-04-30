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
        @(posedge vif.ACLK);    // wait one cycle after reset
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
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.AWVALID <= 0;
            end else begin
                if (aw_queue.size() > 0 && !vif.AWVALID) begin
                    axi_seq_item cur = aw_queue.pop_front();
                    vif.AWID    <= cur.id;
                    vif.AWADDR  <= cur.addr;
                    vif.AWLEN   <= cur.len;
                    vif.AWSIZE  <= cur.size;
                    vif.AWBURST <= cur.burst;
                    vif.AWVALID <= 1;
                    w_queue.push_back(cur);    // mirror to W queue
                end else if (vif.AWVALID && vif.AWREADY) begin
                    vif.AWVALID <= 0;
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
                @(posedge vif.ACLK);
                if (!vif.ARESETn) begin
                    vif.WVALID <= 0;
                    vif.WLAST  <= 0;
                    break;
                end

                vif.WDATA  <= cur.wdata[beat];
                vif.WSTRB  <= cur.wstrb[beat];
                vif.WLAST  <= (beat == cur.len);
                vif.WVALID <= 1;

                while (!vif.WREADY)
                    @(posedge vif.ACLK);
            end

            vif.WVALID <= 0;
            vif.WLAST  <= 0;
        end
    endtask

    // ----------------------------------------------------------------
    // B channel — accept write response
    // ----------------------------------------------------------------
    task drive_b_channel();
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.BREADY <= 0;
            end else begin
                vif.BREADY <= 1;    // always ready to accept response
                if (vif.BVALID && vif.BREADY) begin
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
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.ARVALID <= 0;
            end else begin
                if (ar_queue.size() > 0 && !vif.ARVALID) begin
                    axi_seq_item cur = ar_queue.pop_front();
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

    // ----------------------------------------------------------------
    // R channel — accept read data beat by beat
    // ----------------------------------------------------------------
    task drive_r_channel();
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.RREADY <= 0;
            end else begin
                vif.RREADY <= 1;    // always ready to accept data
                if (vif.RVALID && vif.RREADY) begin
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
            @(posedge vif.ACLK);                             // 再等一拍穩定
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
