`ifndef AXI_SLAVE_MONITOR_SV
`define AXI_SLAVE_MONITOR_SV

class axi_slave_monitor extends axi_monitor_base;
    `uvm_component_utils(axi_slave_monitor)

    // Pending AR transactions waiting for R data (keyed by ARID)
    axi_seq_item    ar_pending_q[*];    // associative array: id -> txn
    int             ar_beat_cnt[*];     // beat counter per id

    function new(string name = "axi_slave_monitor", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        wait (!vif.ARESETn);
        wait ( vif.ARESETn);

        fork
            monitor_aw_w_b();   // Write path: AW + W + B
            monitor_ar_r();     // Read  path: AR + R
        join
    endtask

    // ----------------------------------------------------------------
    // Write path: collect AW info, W beats, then B response
    // ----------------------------------------------------------------
    task monitor_aw_w_b();
        axi_seq_item    aw_q[$];
        axi_seq_item    cur_aw;
        int             w_beat;

        w_beat = 0;

        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                aw_q.delete();
                w_beat = 0;
                continue;
            end

            // ---- AW handshake ----
            if (vif.AWVALID && vif.AWREADY) begin
                axi_seq_item t = axi_seq_item::type_id::create("aw_txn");
                t.write  = 1;
                t.id     = vif.AWID;
                t.addr   = vif.AWADDR;
                t.len    = vif.AWLEN;
                t.size   = vif.AWSIZE;
                t.burst  = vif.AWBURST;
                t.wdata  = new[vif.AWLEN + 1];
                t.wstrb  = new[vif.AWLEN + 1];
                aw_q.push_back(t);
            end

            // ---- W handshake ----
            if (vif.WVALID && vif.WREADY && aw_q.size() > 0) begin
                cur_aw = aw_q[0];
                cur_aw.wdata[w_beat] = vif.WDATA;
                cur_aw.wstrb[w_beat] = vif.WSTRB;
                aw_q[0] = cur_aw;

                if (vif.WLAST) begin
                    w_beat = 0;
                end else begin
                    w_beat++;
                end
            end

            // ---- B handshake ----
            if (vif.BVALID && vif.BREADY) begin
                if (aw_q.size() > 0) begin
                    cur_aw       = aw_q.pop_front();
                    cur_aw.bresp = vif.BRESP;
                    // txn.print();
                    port.write(cur_aw);
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // Read path: collect AR info, then R beats until RLAST
    // ----------------------------------------------------------------
    task monitor_ar_r();
        forever begin
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                ar_pending_q.delete();
                ar_beat_cnt.delete();
                continue;
            end

            // ---- AR handshake ----
            if (vif.ARVALID && vif.ARREADY) begin
                axi_seq_item t = axi_seq_item::type_id::create("ar_txn");
                t.write = 0;
                t.id    = vif.ARID;
                t.addr  = vif.ARADDR;
                t.len   = vif.ARLEN;
                t.size  = vif.ARSIZE;
                t.burst = vif.ARBURST;
                t.rdata = new[vif.ARLEN + 1];
                t.rresp = new[vif.ARLEN + 1];
                ar_pending_q[vif.ARID] = t;
                ar_beat_cnt[vif.ARID]  = 0;
            end

            // ---- R handshake ----
            if (vif.RVALID && vif.RREADY) begin
                int unsigned rid;
                rid = vif.RID;

                if (ar_pending_q.exists(rid)) begin
                    int beat;
                    beat = ar_beat_cnt[rid];
                    ar_pending_q[rid].rdata[beat] = vif.RDATA;
                    ar_pending_q[rid].rresp[beat] = vif.RRESP;

                    if (vif.RLAST) begin
                        // txn.print();
                        port.write(ar_pending_q[rid]);
                        ar_pending_q.delete(rid);
                        ar_beat_cnt.delete(rid);
                    end else begin
                        ar_beat_cnt[rid]++;
                    end
                end else begin
                    `uvm_error("SLVMON", $sformatf("R beat with unknown RID=0x%h", rid))
                end
            end
        end
    endtask

endclass

`endif
