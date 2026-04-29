`ifndef AXI_SCOREBOARD_SV
`define AXI_SCOREBOARD_SV

`include "axi_define.svh"

class axi_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi_scoreboard)

    logic [`D_DATA_WIDTH-1:0]                           mem [`D_MEM_SIZE-1:0];
    uvm_analysis_imp #(axi_seq_item, axi_scoreboard)    imp;

    function new(string name = "axi_scoreboard", uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
        foreach (mem[i]) mem[i] = 0;
    endfunction : build_phase

    virtual function void write(axi_seq_item txn);
        // --------------------------------------------------------
        // AXI monitor 送來的 txn 已是完整一筆 burst：
        //   - write=1 : WDATA[]、WSTRB[] 已填好，BRESP 已收到
        //   - write=0 : RDATA[]、RRESP[] 已填好
        // --------------------------------------------------------

        if (txn.write) begin
            // ---- Write: apply WSTRB 逐 beat 寫入 shadow mem ----
            if (txn.bresp !== `BRESP_OKAY) begin
                `uvm_error(
                    "BRESP_ERR",
                    $sformatf("Write addr=0x%h id=0x%h: bresp=0x%h (not OKAY)",
                              txn.addr, txn.id, txn.bresp)
                )
                return;
            end

            for (int beat = 0; beat <= txn.len; beat++) begin
                int unsigned word_idx;
                logic [`D_ADDR_WIDTH-1:0] beat_addr;

                beat_addr = txn.addr + beat * (1 << txn.size);  // INCR burst
                word_idx  = beat_addr >> $clog2(`D_DATA_WIDTH/8);

                for (int b = 0; b < `D_DATA_WIDTH/8; b++) begin
                    if (txn.wstrb[beat][b])
                        mem[word_idx][b*8 +: 8] = txn.wdata[beat][b*8 +: 8];
                end
            end

            `uvm_info(
                "WRITE_OK",
                $sformatf("Write addr=0x%h id=0x%h len=%0d OK",
                          txn.addr, txn.id, txn.len),
                UVM_LOW
            )

        end else begin
            // ---- Read: 逐 beat 比對 shadow mem ----
            for (int beat = 0; beat <= txn.len; beat++) begin
                int unsigned word_idx;
                logic [`D_ADDR_WIDTH-1:0] beat_addr;
                logic [`D_DATA_WIDTH-1:0] exp_data;

                beat_addr = txn.addr + beat * (1 << txn.size);  // INCR burst
                word_idx  = beat_addr >> $clog2(`D_DATA_WIDTH/8);
                exp_data  = mem[word_idx];

                if (txn.rresp[beat] !== `RRESP_OKAY) begin
                    `uvm_error(
                        "RRESP_ERR",
                        $sformatf("Read addr=0x%h id=0x%h beat=%0d: rresp=0x%h (not OKAY)",
                                  txn.addr, txn.id, beat, txn.rresp[beat])
                    )
                    continue;
                end

                if (exp_data !== txn.rdata[beat]) begin
                    `uvm_fatal(
                        "DATA_MISMATCH",
                        $sformatf("Read addr=0x%h id=0x%h beat=%0d: got=0x%h exp=0x%h",
                                  txn.addr, txn.id, beat, txn.rdata[beat], exp_data)
                    )
                end else begin
                    `uvm_info(
                        "DATA_MATCH",
                        $sformatf("Read addr=0x%h id=0x%h beat=%0d: data=0x%h OK",
                                  txn.addr, txn.id, beat, txn.rdata[beat]),
                        UVM_LOW
                    )
                end
            end
        end

    endfunction

endclass

`endif
