// =============================================================================
// cdc_scoreboard.sv
// Scoreboard：比對 Write Monitor 寫入的資料 vs Read Monitor 讀出的資料
//
// 關鍵設計：
//   Write Monitor 和 Read Monitor 跑在不同時脈域，
//   必須用兩個獨立的 uvm_tlm_analysis_fifo 各自緩衝，
//   再在 scoreboard 的 run_phase 裡同步比對。
//   不能假設兩邊資料同時到達！
// =============================================================================
`include "uvm_macros.svh"
import uvm_pkg::*;
import cdc_fifo_pkg::*;

class cdc_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(cdc_scoreboard)

    // 兩個 analysis export，分別接 write/read monitor
    uvm_analysis_export #(fifo_write_item) write_export;
    uvm_analysis_export #(fifo_read_item)  read_export;

    // 內部 FIFO buffer，讓兩個 domain 的資料各自排隊
    uvm_tlm_analysis_fifo #(fifo_write_item) write_q;
    uvm_tlm_analysis_fifo #(fifo_read_item)  read_q;

    // 統計
    int unsigned pass_cnt;
    int unsigned fail_cnt;
    int unsigned total_written;
    int unsigned total_read;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        write_export = new("write_export", this);
        read_export  = new("read_export",  this);
        write_q      = new("write_q",      this);
        read_q       = new("read_q",       this);
    endfunction

    function void connect_phase(uvm_phase phase);
        // export → internal FIFO（自動 write/get）
        write_export.connect(write_q.analysis_export);
        read_export.connect(read_q.analysis_export);
    endfunction

    // ─── 主比對邏輯 ──────────────────────────────────────────────────────
    task run_phase(uvm_phase phase);
        fifo_write_item wr_tr;
        fifo_read_item  rd_tr;

        forever begin
            // 等兩邊各有一筆（blocking get）
            // 兩個 get 順序固定：先等 write，再等 read
            // 符合 FIFO 先進先出語意
            write_q.get(wr_tr);
            total_written++;

            read_q.get(rd_tr);
            total_read++;

            // 比對
            if (rd_tr.data === wr_tr.data) begin
                pass_cnt++;
                `uvm_info("SB",
                    $sformatf("[PASS #%0d] wrote=0x%02h read=0x%02h",
                              pass_cnt, wr_tr.data, rd_tr.data),
                    UVM_MEDIUM)
            end else begin
                fail_cnt++;
                `uvm_error("SB",
                    $sformatf("[FAIL #%0d] wrote=0x%02h read=0x%02h — MISMATCH!",
                              fail_cnt, wr_tr.data, rd_tr.data))
            end
        end
    endtask

    // ─── 最終報告 ─────────────────────────────────────────────────────────
    function void report_phase(uvm_phase phase);
        `uvm_info("SB", $sformatf(
            "\n========= Scoreboard Report =========\n"  +
            "  Total written : %0d\n"                     +
            "  Total read    : %0d\n"                     +
            "  PASS          : %0d\n"                     +
            "  FAIL          : %0d\n"                     +
            "=====================================",
            total_written, total_read, pass_cnt, fail_cnt),
            UVM_NONE)

        if (fail_cnt > 0)
            `uvm_error("SB", "TEST FAILED — data mismatch detected!")
        else if (total_written == 0)
            `uvm_warning("SB", "No transactions observed!")
        else
            `uvm_info("SB", "TEST PASSED", UVM_NONE)
    endfunction

endclass
