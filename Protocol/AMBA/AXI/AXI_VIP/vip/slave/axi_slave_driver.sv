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
        @(posedge vif.ARESETn);
        @(posedge vif.ACLK);
        fork
            drive_aw_w_b();
            drive_ar_r();
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
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.AWREADY <= 0;
                vif.WREADY  <= 0;
                vif.BVALID  <= 0;
                vif.BRESP   <= `BRESP_OKAY;
                vif.BID     <= '0;
                aw_q.delete();
                w_beat = 0;
                continue;
            end

            // ---- AW channel: always ready ----
            vif.AWREADY <= 1;
            if (vif.AWVALID) begin
                aw_info_t info;
                info.addr  = vif.AWADDR;
                info.size  = vif.AWSIZE;
                info.len   = vif.AWLEN;
                info.burst = vif.AWBURST;
                info.id    = vif.AWID;
                aw_q.push_back(info);
            end

            // ---- W channel: ready when AW descriptor exists ----
            vif.WREADY <= (aw_q.size() > 0);
            if (vif.WVALID && aw_q.size() > 0) begin
                int unsigned word_idx;

                if (w_beat == 0)
                    cur_aw = aw_q[0];

                word_idx = cur_aw.addr >> BYTE_OFFSET_BITS;

                for (int b = 0; b < `D_DATA_WIDTH/8; b++) begin
                    if (vif.WSTRB[b])
                        mem[word_idx][b*8 +: 8] = vif.WDATA[b*8 +: 8];
                end

                if (vif.WLAST) begin
                    void'(aw_q.pop_front());
                    w_beat = 0;
                end else begin
                    cur_aw.addr = cur_aw.addr + (1 << cur_aw.size);
                    aw_q[0]     = cur_aw;
                    w_beat++;
                end
            end

            // ---- B channel: send response after WLAST ----
            if (!vif.BVALID) begin
                if (vif.WVALID && vif.WLAST) begin
                    vif.BVALID <= 1;
                    vif.BRESP  <= `BRESP_OKAY;
                    vif.BID    <= cur_aw.id;
                end
            end else begin
                if (vif.BREADY)
                    vif.BVALID <= 0;
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
            @(posedge vif.ACLK);
            if (!vif.ARESETn) begin
                vif.ARREADY <= 0;
                vif.RVALID  <= 0;
                vif.RDATA   <= '0;
                vif.RRESP   <= `RRESP_OKAY;
                vif.RID     <= '0;
                vif.RLAST   <= 0;
                ar_q.delete();
                continue;
            end

            // ---- AR channel: always ready ----
            vif.ARREADY <= 1;
            if (vif.ARVALID) begin
                ar_info_t info;
                info.addr  = vif.ARADDR;
                info.size  = vif.ARSIZE;
                info.len   = vif.ARLEN;
                info.burst = vif.ARBURST;
                info.id    = vif.ARID;
                ar_q.push_back(info);
            end

            // ---- R channel: serve head of AR queue ----
            if (vif.RVALID && vif.RREADY && vif.RLAST) begin
                vif.RVALID <= 0;
                vif.RLAST  <= 0;
            end else if (ar_q.size() > 0 && (!vif.RVALID || vif.RREADY)) begin
                ar_info_t rd;
                int unsigned word_idx;

                rd       = ar_q[0];
                word_idx = rd.addr >> BYTE_OFFSET_BITS;

                vif.RDATA  <= mem[word_idx];
                vif.RRESP  <= `RRESP_OKAY;
                vif.RID    <= rd.id;
                vif.RLAST  <= (rd.len == 0);
                vif.RVALID <= 1;

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
