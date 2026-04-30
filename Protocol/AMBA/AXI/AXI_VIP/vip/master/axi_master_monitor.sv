`ifndef AXI_MASTER_MONITOR_SV
`define AXI_MASTER_MONITOR_SV

class axi_master_monitor extends axi_monitor_base;
    `uvm_component_utils(axi_master_monitor)

    // Pending AR transactions waiting for R data (keyed by ARID)
    axi_seq_item    ar_pending_q[int][$];  // associative array: id -> queue of txn
    int             ar_beat_cnt[int];      // beat counter per id

    function new(string name = "axi_master_monitor", uvm_component parent);
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
        axi_seq_item    aw_q[$];        // AW descriptors in order
        axi_seq_item    cur_aw;
        int             w_beat;

        w_beat = 0;

        forever begin
            @(vif.monitor_cb);
            if (!vif.ARESETn) begin
                aw_q.delete();
                w_beat = 0;
                continue;
            end

            // ---- AW handshake ----
            if (vif.monitor_cb.AWVALID && vif.monitor_cb.AWREADY) begin
                axi_seq_item t = axi_seq_item::type_id::create("aw_txn");
                t.write  = 1;
                t.id     = vif.monitor_cb.AWID;
                t.addr   = vif.monitor_cb.AWADDR;
                t.len    = vif.monitor_cb.AWLEN;
                t.size   = vif.monitor_cb.AWSIZE;
                t.burst  = vif.monitor_cb.AWBURST;
                t.wdata  = new[vif.monitor_cb.AWLEN + 1];
                t.wstrb  = new[vif.monitor_cb.AWLEN + 1];
                aw_q.push_back(t);
            end

            // ---- W handshake ----
            if (vif.monitor_cb.WVALID && vif.monitor_cb.WREADY) begin
                // 等到 aw_q 有 descriptor 才處理
                if (aw_q.size() > 0) begin
                    // 防呆：beat 不能超過當前 descriptor 的 len
                    if (w_beat <= aw_q[0].len) begin
                        aw_q[0].wdata[w_beat] = vif.monitor_cb.WDATA;
                        aw_q[0].wstrb[w_beat] = vif.monitor_cb.WSTRB;
                    end else begin
                        `uvm_error("MSTMON", $sformatf(
                            "W beat %0d exceeds AWLEN=%0d, dropping beat (addr: %0d)", w_beat, aw_q[0].len, aw_q[0].addr))
                    end

                    if (vif.monitor_cb.WLAST) begin
                        w_beat = 0;
                        // WLAST 到了才等 B response，不在這裡 pop
                    end else begin
                        w_beat++;
                    end
                end else begin
                    `uvm_error("MSTMON", "W beat received but aw_q is empty")
                end
            end

            // ---- B handshake ----
            if (vif.monitor_cb.BVALID && vif.monitor_cb.BREADY) begin
                if (aw_q.size() > 0) begin
                    axi_seq_item cur;
                    cur       = aw_q.pop_front();   // ← B response 到才 pop，確保順序
                    cur.bresp = vif.monitor_cb.BRESP;
                    port.write(cur);
                end else begin
                    `uvm_error("MSTMON", $sformatf("B response with no pending AW, BID=0x%h", vif.monitor_cb.BID))
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // Read path: collect AR info, then R beats until RLAST  (out-of-order R response: AXI spec 保證同一個 ID 的 R response 順序跟 AR 發出的順序一致, 不同 ID 可以亂序)
    // ----------------------------------------------------------------
    task monitor_ar_r();
        forever begin
            @(vif.monitor_cb);
            if (!vif.ARESETn) begin
                ar_pending_q.delete();
                ar_beat_cnt.delete();
                continue;
            end

            // ---- AR handshake（先處理，確保同拍的 R beat 能找到） ----
            if (vif.monitor_cb.ARVALID && vif.monitor_cb.ARREADY) begin
                axi_seq_item t = axi_seq_item::type_id::create("ar_txn");
                t.write = 0;
                t.id    = vif.monitor_cb.ARID;
                t.addr  = vif.monitor_cb.ARADDR;
                t.len   = vif.monitor_cb.ARLEN;
                t.size  = vif.monitor_cb.ARSIZE;
                t.burst = vif.monitor_cb.ARBURST;
                t.rdata = new[vif.monitor_cb.ARLEN + 1];
                t.rresp = new[vif.monitor_cb.ARLEN + 1];
                ar_pending_q[vif.monitor_cb.ARID].push_back(t);  // ← push 進去，不覆蓋
                if (!ar_beat_cnt.exists(vif.monitor_cb.ARID))
                    ar_beat_cnt[vif.monitor_cb.ARID] = 0;        // ← 只有第一筆才初始化
            end

            // ---- R handshake（AR 之後處理） ----
            if (vif.monitor_cb.RVALID && vif.monitor_cb.RREADY) begin
                int unsigned rid;
                rid = vif.monitor_cb.RID;

                if (ar_pending_q.exists(rid)) begin
                    int beat;
                    beat = ar_beat_cnt[rid];

                    // 防呆：beat 不能超過 rdata 陣列大小
                    if (beat < ar_pending_q[rid][0].rdata.size()) begin
                        ar_pending_q[rid][0].rdata[beat] = vif.monitor_cb.RDATA;
                        ar_pending_q[rid][0].rresp[beat] = vif.monitor_cb.RRESP;
                    end else begin
                        `uvm_error("MSTMON", $sformatf(
                            "R beat %0d exceeds ARLEN=%0d for RID=0x%h",
                            beat, ar_pending_q[rid][0].len, rid))
                    end

                    if (vif.monitor_cb.RLAST) begin
                        port.write(ar_pending_q[rid][0]);
                        ar_pending_q[rid].pop_front();     // ← 這筆做完才 pop
                        if (ar_pending_q[rid].size() == 0)
                            ar_pending_q.delete(rid);      // ← 清乾淨
                        ar_beat_cnt[rid] = 0;              // ← reset beat count 給下一筆用
                    end else begin
                        ar_beat_cnt[rid]++;
                    end
                end else begin
                    `uvm_error("MSTMON", $sformatf("R beat with unknown RID=0x%h", rid))
                end
            end
        end
    endtask

endclass

`endif
