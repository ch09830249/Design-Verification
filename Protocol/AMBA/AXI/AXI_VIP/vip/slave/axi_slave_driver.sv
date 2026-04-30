`ifndef AXI_SLAVE_DRIVER_SV
`define AXI_SLAVE_DRIVER_SV

class axi_slave_driver extends axi_driver_base;
    `uvm_component_utils(axi_slave_driver)

    logic [`D_DATA_WIDTH-1:0]   mem [`D_MEM_SIZE-1:0];

    localparam BYTE_OFFSET_BITS = $clog2(`D_DATA_WIDTH/8);

    function new(string name = "axi_slave_driver", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        foreach (mem[i]) mem[i] = 0;
    endfunction

    virtual task run_phase(uvm_phase phase);
        reset_signal();
        @(posedge vif.ARESETn);    // 等 reset 結束
        @(vif.slave_cb);       // 再等一拍穩定
        fork
            drive_aw_w_b();     // Write path: AW + W + B
            drive_ar_r();       // Read  path: AR + R
        join
    endtask

    // ----------------------------------------------------------------
    // Write path: accept AW, accept W beats, send B response
    // ----------------------------------------------------------------
    task drive_aw_w_b();
        typedef struct {
            logic [`D_ADDR_WIDTH-1:0]   addr;
            logic [2:0]                 size;
            logic [7:0]                 len;
            logic [1:0]                 burst;
            logic [`D_ID_WIDTH-1:0]     id;
        } aw_info_t;

        aw_info_t   aw_q[$];
        aw_info_t   cur_aw;
        int         w_beat;

        w_beat = 0;

        forever begin
            @(vif.slave_cb);
            if (!vif.ARESETn) begin
                vif.slave_cb.AWREADY <= 0;
                vif.slave_cb.WREADY  <= 0;
                vif.slave_cb.BVALID  <= 0;
                vif.slave_cb.BRESP   <= `BRESP_OKAY;
                vif.slave_cb.BID     <= '0;
                aw_q.delete();
                w_beat = 0;
                continue;
            end

            // ---- AW channel: always ready ----
            vif.slave_cb.AWREADY <= 1;
            if (vif.slave_cb.AWVALID) begin
                aw_info_t info;
                info.addr  = vif.slave_cb.AWADDR;
                info.size  = vif.slave_cb.AWSIZE;
                info.len   = vif.slave_cb.AWLEN;
                info.burst = vif.slave_cb.AWBURST;
                info.id    = vif.slave_cb.AWID;
                aw_q.push_back(info);
            end

            // ---- W channel: ready when AW descriptor exists ----
            vif.slave_cb.WREADY <= (aw_q.size() > 0);
            if (vif.slave_cb.WVALID && aw_q.size() > 0) begin
                int unsigned word_idx;

                if (w_beat == 0)
                    cur_aw = aw_q[0];       // 指向第一筆 write

                word_idx = cur_aw.addr >> BYTE_OFFSET_BITS;

                // Apply WSTRB byte-enable
                for (int b = 0; b < `D_DATA_WIDTH/8; b++) begin
                    if (vif.slave_cb.WSTRB[b])
                        mem[word_idx][b*8 +: 8] = vif.slave_cb.WDATA[b*8 +: 8];
                end

                if (vif.slave_cb.WLAST) begin
                    void'(aw_q.pop_front());    // 代表該 transfer 做完了 => w_beat reset into 0
                    w_beat = 0;
                end else begin
                    cur_aw.addr = cur_aw.addr + (1 << cur_aw.size);
                    aw_q[0]     = cur_aw;
                    w_beat++;
                end
            end

            // ---- B channel: send response after WLAST ----
            if (!vif.slave_cb.BVALID) begin
                if (vif.slave_cb.WVALID && vif.slave_cb.WLAST) begin
                    vif.slave_cb.BVALID  <= 1;
                    vif.slave_cb.BRESP   <= `BRESP_OKAY;
                    vif.slave_cb.BID     <= cur_aw.id;
                end
            end else begin
                if (vif.slave_cb.BREADY)
                    vif.slave_cb.BVALID <= 0;
            end
        end
    endtask

    // ----------------------------------------------------------------
    // Read path: accept AR, return R beats
    // ----------------------------------------------------------------
    task drive_ar_r();
        typedef struct {
            logic [`D_ADDR_WIDTH-1:0]   addr;
            logic [2:0]                 size;
            logic [7:0]                 len;
            logic [1:0]                 burst;
            logic [`D_ID_WIDTH-1:0]     id;
        } ar_info_t;

        ar_info_t   ar_q[$];

        forever begin
            @(vif.slave_cb);
            if (!vif.ARESETn) begin
                vif.slave_cb.ARREADY <= 0;
                vif.slave_cb.RVALID  <= 0;
                vif.slave_cb.RDATA   <= '0;
                vif.slave_cb.RRESP   <= `RRESP_OKAY;
                vif.slave_cb.RID     <= '0;
                vif.slave_cb.RLAST   <= 0;
                ar_q.delete();
                continue;
            end

            // ---- AR channel: always ready ----
            vif.slave_cb.ARREADY <= 1;
            if (vif.slave_cb.ARVALID) begin
                ar_info_t info;
                info.addr  = vif.slave_cb.ARADDR;
                info.size  = vif.slave_cb.ARSIZE;
                info.len   = vif.slave_cb.ARLEN;
                info.burst = vif.slave_cb.ARBURST;
                info.id    = vif.slave_cb.ARID;
                ar_q.push_back(info);
            end

            // ---- R channel: serve head of AR queue ----

            if (vif.slave_cb.RVALID && vif.slave_cb.RREADY && vif.slave_cb.RLAST) begin
                // 本 burst 結束，先清 RVALID
                vif.slave_cb.RVALID <= 0;
                vif.slave_cb.RLAST  <= 0;
            end else if (ar_q.size() > 0 && (!vif.slave_cb.RVALID || vif.slave_cb.RREADY)) begin
                ar_info_t rd;
                int unsigned word_idx;

                rd       = ar_q[0];
                word_idx = rd.addr >> BYTE_OFFSET_BITS;

                vif.slave_cb.RDATA  <= mem[word_idx];
                vif.slave_cb.RRESP  <= `RRESP_OKAY;
                vif.slave_cb.RID    <= rd.id;
                vif.slave_cb.RLAST  <= (rd.len == 0);
                vif.slave_cb.RVALID <= 1;

                if (rd.len == 0)
                    void'(ar_q.pop_front());
                else begin
                    ar_q[0].addr = rd.addr + (1 << rd.size);
                    ar_q[0].len  = rd.len - 1;
                end
            end
        end
    endtask

    // ----------------------------------------------------------------
    // Reset
    // ----------------------------------------------------------------
    task reset_signal();
        vif.AWREADY <= 0;
        vif.WREADY  <= 0;
        vif.BVALID  <= 0;
        vif.BRESP   <= `BRESP_OKAY;
        vif.BID     <= '0;
        vif.ARREADY <= 0;
        vif.RVALID  <= 0;
        vif.RDATA   <= '0;
        vif.RRESP   <= `RRESP_OKAY;
        vif.RID     <= '0;
        vif.RLAST   <= 0;
    endtask

endclass

`endif
