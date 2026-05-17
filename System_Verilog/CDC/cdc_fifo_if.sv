// =============================================================================
// cdc_fifo_if.sv
// Virtual interface：含雙時脈 clocking block 與 SVA assertions
// =============================================================================
interface cdc_fifo_if #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
)(
    input logic WCLK,
    input logic RCLK
);

    // ─── Write 端訊號 ─────────────────────────────────────────────────────
    logic                  WRST_N;
    logic                  WINC;
    logic [DATA_WIDTH-1:0] WDATA;
    logic                  WFULL;

    // ─── Read 端訊號 ──────────────────────────────────────────────────────
    logic                  RRST_N;
    logic                  RINC;
    logic [DATA_WIDTH-1:0] RDATA;
    logic                  REMPTY;

    // ─── DUT 內部 Gray Code pointer（連接到 DUT 的 probe）────────────────
    logic [ADDR_WIDTH:0] wptr_gray;
    logic [ADDR_WIDTH:0] rptr_gray;

    // =========================================================================
    // Clocking Blocks：Driver/Monitor 透過 CB 存取，消除 race condition
    // =========================================================================

    // Write 端 Master CB（Driver 用）
    clocking write_cb @(posedge WCLK);
        default input  #1step;
        default output #1;
        output WINC, WDATA, WRST_N;
        input  WFULL;
    endclocking

    // Read 端 Master CB（Driver 用）
    clocking read_cb @(posedge RCLK);
        default input  #1step;
        default output #1;
        output RINC, RRST_N;
        input  RDATA, REMPTY;
    endclocking

    // Write 端 Monitor CB（被動觀察）
    clocking write_mon_cb @(posedge WCLK);
        default input #1step;
        input WINC, WDATA, WRST_N, WFULL, wptr_gray;
    endclocking

    // Read 端 Monitor CB（被動觀察）
    clocking read_mon_cb @(posedge RCLK);
        default input #1step;
        input RINC, RRST_N, RDATA, REMPTY, rptr_gray;
    endclocking

    // =========================================================================
    // SVA Assertions
    // =========================================================================

    // 1. WFULL 期間，wptr_gray 不應移動（DUT 必須忽略 WINC）
    property p_no_write_when_full;
        @(posedge WCLK) disable iff (!WRST_N)
        (WFULL && WINC) |=> $stable(wptr_gray);
    endproperty
    AP_NO_WRITE_WHEN_FULL: assert property (p_no_write_when_full)
        else $error("[ASSERT] Write pointer moved while WFULL=1!");

    // 2. REMPTY 期間，rptr_gray 不應移動（DUT 必須忽略 RINC）
    property p_no_read_when_empty;
        @(posedge RCLK) disable iff (!RRST_N)
        (REMPTY && RINC) |=> $stable(rptr_gray);
    endproperty
    AP_NO_READ_WHEN_EMPTY: assert property (p_no_read_when_empty)
        else $error("[ASSERT] Read pointer moved while REMPTY=1!");

    // 3. Gray Code 安全性：每次 pointer 改變只有 1 個 bit 不同
    //    這是 CDC 安全的核心保證
    property p_wptr_gray_one_hot;
        @(posedge WCLK) disable iff (!WRST_N)
        $changed(wptr_gray) |->
            $onehot(wptr_gray ^ $past(wptr_gray));
    endproperty
    AP_WPTR_GRAY_ONE_HOT: assert property (p_wptr_gray_one_hot)
        else $error("[ASSERT] wptr_gray changed more than 1 bit — CDC unsafe!");

    property p_rptr_gray_one_hot;
        @(posedge RCLK) disable iff (!RRST_N)
        $changed(rptr_gray) |->
            $onehot(rptr_gray ^ $past(rptr_gray));
    endproperty
    AP_RPTR_GRAY_ONE_HOT: assert property (p_rptr_gray_one_hot)
        else $error("[ASSERT] rptr_gray changed more than 1 bit — CDC unsafe!");

    // 4. WFULL 與 REMPTY 不可同時為 1（語意矛盾）
    property p_no_full_and_empty;
        @(posedge WCLK) disable iff (!WRST_N)
        not (WFULL && REMPTY);
    endproperty
    AP_NO_FULL_AND_EMPTY: assert property (p_no_full_and_empty)
        else $error("[ASSERT] WFULL and REMPTY both high simultaneously!");

    // 5. Reset 後 pointer 必須歸零
    property p_reset_clears_wptr;
        @(posedge WCLK)
        $fell(WRST_N) |=> (wptr_gray == 0);
    endproperty
    AP_RESET_CLEARS_WPTR: assert property (p_reset_clears_wptr)
        else $error("[ASSERT] wptr_gray not cleared after WRST_N de-assertion!");

    property p_reset_clears_rptr;
        @(posedge RCLK)
        $fell(RRST_N) |=> (rptr_gray == 0);
    endproperty
    AP_RESET_CLEARS_RPTR: assert property (p_reset_clears_rptr)
        else $error("[ASSERT] rptr_gray not cleared after RRST_N de-assertion!");

    // 6. WFULL 後資料不應遺失（WFULL 解除前 RDATA 必須有效）
    //    此 assertion 為 cover property（覆蓋率目標而非錯誤檢查）
    cover property (
        @(posedge WCLK) disable iff (!WRST_N)
        $rose(WFULL) ##[1:32] $fell(WFULL)
    );

endinterface
