// =============================================================================
// top_tb.sv
// Top-level testbench
// 產生兩個獨立時脈：WCLK=200MHz(2.5ns)、RCLK=133MHz(3.76ns)
// 兩個時脈完全非同步，相位關係不固定
// =============================================================================
`timescale 1ns/1ps

`include "uvm_macros.svh"
import uvm_pkg::*;
import cdc_fifo_pkg::*;

// ─── 所有元件 include ────────────────────────────────────────────────────────
`include "cdc_fifo_if.sv"
`include "cdc_write_agent.sv"
`include "cdc_read_agent.sv"
`include "cdc_scoreboard.sv"
`include "cdc_env_seq_tests.sv"

module top_tb;

    // ─── 時脈產生：兩個完全獨立的時脈 ──────────────────────────────────
    logic WCLK, RCLK;

    // Write CLK：200 MHz → 週期 5ns（half=2.5ns）
    initial WCLK = 1'b0;
    always #2.5 WCLK = ~WCLK;

    // Read CLK：133 MHz → 週期 7.52ns（half=3.76ns）
    // 故意延遲 1ns 讓兩個時脈相位不對齊
    initial begin
        #1;
        RCLK = 1'b0;
    end
    always #3.76 RCLK = ~RCLK;

    // ─── Interface 實例化 ────────────────────────────────────────────────
    cdc_fifo_if #(
        .DATA_WIDTH(DATA_WIDTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) fifo_if (
        .WCLK(WCLK),
        .RCLK(RCLK)
    );

    // ─── DUT 實例化 ──────────────────────────────────────────────────────
    async_fifo #(
        .DATA_WIDTH(DATA_WIDTH),
        .DEPTH     (FIFO_DEPTH),
        .ADDR_WIDTH(ADDR_WIDTH)
    ) dut (
        // Write 端
        .WCLK   (WCLK),
        .WRST_N (fifo_if.WRST_N),
        .WINC   (fifo_if.WINC),
        .WDATA  (fifo_if.WDATA),
        .WFULL  (fifo_if.WFULL),
        // Read 端
        .RCLK   (RCLK),
        .RRST_N (fifo_if.RRST_N),
        .RINC   (fifo_if.RINC),
        .RDATA  (fifo_if.RDATA),
        .REMPTY (fifo_if.REMPTY)
    );

    // ─── Gray Code pointer probe（連到 interface 的 assertion）──────────
    // 直接連接 DUT 內部訊號，讓 SVA 可以觀察
    assign fifo_if.wptr_gray = dut.wptr_gray;
    assign fifo_if.rptr_gray = dut.rptr_gray;

    // ─── 初始化訊號 ──────────────────────────────────────────────────────
    initial begin
        fifo_if.WRST_N = 1'b0;
        fifo_if.RRST_N = 1'b0;
        fifo_if.WINC   = 1'b0;
        fifo_if.WDATA  = 8'h00;
        fifo_if.RINC   = 1'b0;
    end

    // ─── config_db 設定 ──────────────────────────────────────────────────
    initial begin
        // 所有層級都可取得 vif
        uvm_config_db #(virtual cdc_fifo_if)::set(
            null, "uvm_test_top*", "vif", fifo_if);

        // 設定兩個 agent 為 ACTIVE mode
        uvm_config_db #(uvm_active_passive_enum)::set(
            null, "uvm_test_top.env.write_agent", "is_active", UVM_ACTIVE);
        uvm_config_db #(uvm_active_passive_enum)::set(
            null, "uvm_test_top.env.read_agent",  "is_active", UVM_ACTIVE);

        // 執行 UVM test（用 +UVM_TESTNAME 指定）
        run_test();
    end

    // ─── Waveform dump ───────────────────────────────────────────────────
    initial begin
        $dumpfile("cdc_fifo.vcd");
        $dumpvars(0, top_tb);
    end

    // ─── Timeout 保護 ────────────────────────────────────────────────────
    initial begin
        #500_000ns;
        `uvm_fatal("TIMEOUT", "Simulation timeout — check for hang!")
        $finish;
    end

endmodule
