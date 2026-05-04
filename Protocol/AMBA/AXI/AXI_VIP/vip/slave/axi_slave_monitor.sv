`ifndef AXI_SLAVE_MONITOR_SV
`define AXI_SLAVE_MONITOR_SV

class axi_slave_monitor extends axi_monitor_base;
    `uvm_component_utils(axi_slave_monitor)

    axi_seq_item    ar_pending_q[int][$];  // associative array: id -> queue of txn
    int             ar_beat_cnt[int];      // beat counter per id

    function new(string name = "axi_slave_monitor", uvm_component parent);
        super.new(name, parent);
    endfunction

    virtual task run_phase(uvm_phase phase);
        wait (!vif.ARESETn);
        wait ( vif.ARESETn);

        fork
            monitor_aw_w_b();
            monitor_ar_r();
        join
    endtask

    task monitor_aw_w_b();
        axi_seq_item    aw_q[$];
        axi_seq_item    cur_aw;
        int             w_beat;

        w_beat = 0;

        forever begin
            @(vif.ACLK);
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
            if (vif.WVALID && vif.WREADY) begin
                if (aw_q.size() > 0) begin
                    if (w_beat <= aw_q[0].len) begin
                        aw_q[0].wdata[w_beat] = vif.WDATA;
                        aw_q[0].wstrb[w_beat] = vif.WSTRB;
                    end else begin
                        `uvm_error("SLVMON", $sformatf(
                            "W beat %0d exceeds AWLEN=%0d, dropping beat", w_beat, aw_q[0].len))
                    end

                    if (vif.WLAST)  w_beat = 0;
                    else            w_beat++;
                end else begin
                    `uvm_error("SLVMON", "W beat received but aw_q is empty")
                end
            end

            // ---- B handshake ----
            if (vif.BVALID && vif.BREADY) begin
                if (aw_q.size() > 0) begin
                    cur_aw       = aw_q.pop_front();
                    cur_aw.bresp = vif.BRESP;
                    port.write(cur_aw);
                end else begin
                    `uvm_error("SLVMON", $sformatf("B response with no pending AW, BID=0x%h", vif.BID))
                end
            end
        end
    endtask

    task monitor_ar_r();
        forever begin
            @(vif.ACLK);
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
                ar_pending_q[vif.ARID].push_back(t);
                if (!ar_beat_cnt.exists(vif.ARID))
                    ar_beat_cnt[vif.ARID] = 0;
            end

            // ---- R handshake ----
            if (vif.RVALID && vif.RREADY) begin
                int unsigned rid;
                rid = vif.RID;

                if (ar_pending_q.exists(rid)) begin
                    int beat;
                    beat = ar_beat_cnt[rid];

                    if (beat < ar_pending_q[rid][0].rdata.size()) begin
                        ar_pending_q[rid][0].rdata[beat] = vif.RDATA;
                        ar_pending_q[rid][0].rresp[beat] = vif.RRESP;
                    end else begin
                        `uvm_error("SLVMON", $sformatf(
                            "R beat %0d exceeds ARLEN=%0d for RID=0x%h",
                            beat, ar_pending_q[rid][0].len, rid))
                    end

                    if (vif.RLAST) begin
                        port.write(ar_pending_q[rid][0]);
                        ar_pending_q[rid].pop_front();
                        if (ar_pending_q[rid].size() == 0)
                            ar_pending_q.delete(rid);
                        ar_beat_cnt[rid] = 0;
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
