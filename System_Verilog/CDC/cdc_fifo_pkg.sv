// =============================================================================
// cdc_fifo_pkg.sv
// 共用 package：參數、transaction item、型別定義
// =============================================================================
package cdc_fifo_pkg;

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // ─── 全域參數 ─────────────────────────────────────────────────────────
    parameter int DATA_WIDTH = 8;
    parameter int FIFO_DEPTH = 16;
    parameter int ADDR_WIDTH = 4;   // $clog2(FIFO_DEPTH)

    // ─── 同步延遲容忍（Two-FF synchronizer 需要 2 個目標域週期）────────
    parameter int SYNC_LATENCY = 2;

    // =========================================================================
    // Write Transaction Item
    // =========================================================================
    class fifo_write_item extends uvm_sequence_item;
        `uvm_object_utils(fifo_write_item)

        rand logic [DATA_WIDTH-1:0] data;
        rand int unsigned            gap_cycles; // 寫入之間的空閒週期數

        constraint c_gap { gap_cycles inside {[0:3]}; }

        function new(string name = "fifo_write_item");
            super.new(name);
        endfunction

        function string convert2string();
            return $sformatf("WRITE data=0x%02h gap=%0d", data, gap_cycles);
        endfunction
    endclass

    // =========================================================================
    // Read Transaction Item
    // =========================================================================
    class fifo_read_item extends uvm_sequence_item;
        `uvm_object_utils(fifo_read_item)

        logic [DATA_WIDTH-1:0] data;      // 由 monitor 填入
        rand int unsigned       gap_cycles;

        constraint c_gap { gap_cycles inside {[0:3]}; }

        function new(string name = "fifo_read_item");
            super.new(name);
        endfunction

        function string convert2string();
            return $sformatf("READ  data=0x%02h gap=%0d", data, gap_cycles);
        endfunction
    endclass

endpackage
