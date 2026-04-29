`ifndef AXI_SLAVE_BFM_SV
`define AXI_SLAVE_BFM_SV

`include "axi_define.svh"

module axi_slave_bfm
(
    input   logic       ACLK,
    input   logic       ARESETn,
    axi_interface       vif
);

    // --------------------------------------------------------
    // Internal memory
    // --------------------------------------------------------
    logic [`D_DATA_WIDTH-1:0]   mem [`D_MEM_SIZE-1:0];

    localparam BYTE_OFFSET_BITS = $clog2(`D_DATA_WIDTH/8);

    // --------------------------------------------------------
    // Write channel state
    // --------------------------------------------------------
    typedef struct {
        logic [`D_ADDR_WIDTH-1:0]   addr;
        logic [2:0]                 size;
        logic [7:0]                 len;
        logic [1:0]                 burst;
        logic [`D_ID_WIDTH-1:0]     id;
    } aw_info_t;

    aw_info_t   aw_q [$];  // AW channel queue
    aw_info_t   cur_aw;
    int         w_beat;

    // --------------------------------------------------------
    // Read channel state
    // --------------------------------------------------------
    typedef struct {
        logic [`D_ADDR_WIDTH-1:0]   addr;
        logic [2:0]                 size;
        logic [7:0]                 len;
        logic [1:0]                 burst;
        logic [`D_ID_WIDTH-1:0]     id;
    } ar_info_t;

    ar_info_t   ar_q [$];  // AR channel queue

    // --------------------------------------------------------
    // Byte address → aligned word address helper
    // --------------------------------------------------------
    function automatic [`D_ADDR_WIDTH-1:0] word_addr(
        input logic [`D_ADDR_WIDTH-1:0] byte_addr
    );
        return byte_addr >> BYTE_OFFSET_BITS;
    endfunction

    // --------------------------------------------------------
    // AXI INCR burst next-address helper
    // --------------------------------------------------------
    function automatic [`D_ADDR_WIDTH-1:0] next_addr(
        input logic [`D_ADDR_WIDTH-1:0] cur,
        input logic [2:0]               size
    );
        return cur + (1 << size);
    endfunction

    // --------------------------------------------------------
    // Init
    // --------------------------------------------------------
    initial begin
        foreach (mem[i]) mem[i] = '0;

        // Drive default handshake signals
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
    end

    // ========================================================
    // AW channel — accept write address
    // ========================================================
    always @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            vif.AWREADY <= 0;
        end else begin
            vif.AWREADY <= 1;  // always ready (pipeline-friendly)

            if (vif.AWVALID && vif.AWREADY) begin
                aw_info_t info;
                info.addr  = vif.AWADDR;
                info.size  = vif.AWSIZE;
                info.len   = vif.AWLEN;
                info.burst = vif.AWBURST;
                info.id    = vif.AWID;
                aw_q.push_back(info);
            end
        end
    end

    // ========================================================
    // W channel — accept write data, write to memory
    // ========================================================
    always @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            vif.WREADY <= 0;
            w_beat     <= 0;
        end else begin
            vif.WREADY <= (aw_q.size() > 0);  // ready when we have an AW descriptor

            if (vif.WVALID && vif.WREADY && aw_q.size() > 0) begin
                if (w_beat == 0)
                    cur_aw = aw_q[0];  // peek front

                // Write with byte-enable
                for (int b = 0; b < `D_DATA_WIDTH/8; b++) begin
                    if (vif.WSTRB[b])
                        mem[word_addr(cur_aw.addr)][b*8 +: 8] <= vif.WDATA[b*8 +: 8];
                end

                if (vif.WLAST) begin
                    void'(aw_q.pop_front());  // done with this descriptor
                    w_beat <= 0;
                end else begin
                    // Advance address for next beat (INCR burst only)
                    cur_aw.addr = next_addr(cur_aw.addr, cur_aw.size);
                    aw_q[0]     = cur_aw;
                    w_beat      <= w_beat + 1;
                end
            end
        end
    end

    // ========================================================
    // B channel — send write response
    // ========================================================
    always @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            vif.BVALID <= 0;
            vif.BRESP  <= `BRESP_OKAY;
            vif.BID    <= '0;
        end else begin
            // Issue BRESP one cycle after WLAST is accepted
            if (!vif.BVALID) begin
                if (vif.WVALID && vif.WREADY && vif.WLAST) begin
                    vif.BVALID <= 1;
                    vif.BRESP  <= `BRESP_OKAY;
                    vif.BID    <= vif.AWID;  // mirror ID
                end
            end else begin
                if (vif.BREADY)
                    vif.BVALID <= 0;
            end
        end
    end

    // ========================================================
    // AR channel + R channel — read address & return data
    // ========================================================
    always @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            vif.ARREADY <= 0;
            vif.RVALID  <= 0;
            vif.RDATA   <= '0;
            vif.RRESP   <= `RRESP_OKAY;
            vif.RID     <= '0;
            vif.RLAST   <= 0;
        end else begin
            vif.ARREADY <= 1;

            if (vif.ARVALID && vif.ARREADY) begin
                ar_info_t info;
                info.addr  = vif.ARADDR;
                info.size  = vif.ARSIZE;
                info.len   = vif.ARLEN;
                info.burst = vif.ARBURST;
                info.id    = vif.ARID;
                ar_q.push_back(info);
            end

            // Drive R channel from head of AR queue
            if (ar_q.size() > 0 && (!vif.RVALID || vif.RREADY)) begin
                ar_info_t rd;
                rd = ar_q[0];

                // Read data (aligned word)
                vif.RDATA  <= mem[word_addr(rd.addr)];
                vif.RRESP  <= `RRESP_OKAY;
                vif.RID    <= rd.id;
                vif.RLAST  <= (rd.len == 0);
                vif.RVALID <= 1;

                if (rd.len == 0) begin
                    void'(ar_q.pop_front());
                end else begin
                    // Advance for next beat
                    ar_q[0].addr = next_addr(rd.addr, rd.size);
                    ar_q[0].len  = rd.len - 1;
                end
            end else if (vif.RVALID && vif.RREADY && vif.RLAST) begin
                vif.RVALID <= 0;
            end
        end
    end

endmodule

`endif
