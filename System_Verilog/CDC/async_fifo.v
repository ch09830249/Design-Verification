// =============================================================================
// async_fifo.v
// Asynchronous FIFO  –  深度 16，資料寬度 8-bit
// Write 端：CLK_W (200 MHz)
// Read  端：CLK_R (133 MHz)
// Pointer 以 Gray Code 跨域同步，確保 CDC 安全
// =============================================================================
module async_fifo #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH      = 16,           // 必須是 2 的次方
    parameter ADDR_WIDTH = $clog2(DEPTH) // = 4
)(
    // Write 端
    input  wire                  WCLK,
    input  wire                  WRST_N,
    input  wire                  WINC,
    input  wire [DATA_WIDTH-1:0] WDATA,
    output wire                  WFULL,

    // Read 端
    input  wire                  RCLK,
    input  wire                  RRST_N,
    input  wire                  RINC,
    output wire [DATA_WIDTH-1:0] RDATA,
    output wire                  REMPTY
);

    // ─── SRAM（雙埠，單純組合邏輯讀取）──────────────────────────────────
    reg [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // ─── Write/Read pointer（二進位，多一個 bit 用來區分 full/empty）────
    // 實際 pointer 寬度 = ADDR_WIDTH+1，MSB 為 overflow bit
    reg [ADDR_WIDTH:0] wptr_bin, rptr_bin;
    reg [ADDR_WIDTH:0] wptr_gray, rptr_gray;

    // ─── 跨域同步暫存器：write side 同步 rptr，read side 同步 wptr ──────
    // rptr_gray 同步到 WCLK domain
    reg [ADDR_WIDTH:0] rptr_gray_sync1_w, rptr_gray_sync2_w;
    // wptr_gray 同步到 RCLK domain
    reg [ADDR_WIDTH:0] wptr_gray_sync1_r, wptr_gray_sync2_r;

    // ─── 地址（去掉 MSB overflow bit）────────────────────────────────────
    wire [ADDR_WIDTH-1:0] waddr = wptr_bin[ADDR_WIDTH-1:0];
    wire [ADDR_WIDTH-1:0] raddr = rptr_bin[ADDR_WIDTH-1:0];

    // =========================================================================
    // WRITE 端邏輯（WCLK domain）
    // =========================================================================

    // 寫入 SRAM
    always @(posedge WCLK) begin
        if (WINC && !WFULL)
            mem[waddr] <= WDATA;
    end

    // Write pointer 遞增
    always @(posedge WCLK or negedge WRST_N) begin
        if (!WRST_N) begin
            wptr_bin  <= 0;
            wptr_gray <= 0;
        end else if (WINC && !WFULL) begin
            wptr_bin  <= wptr_bin + 1'b1;
            wptr_gray <= bin2gray(wptr_bin + 1'b1);
        end
    end

    // rptr_gray 同步到 WCLK domain（Two-FF Synchronizer）
    always @(posedge WCLK or negedge WRST_N) begin
        if (!WRST_N) begin
            rptr_gray_sync1_w <= 0;
            rptr_gray_sync2_w <= 0;
        end else begin
            rptr_gray_sync1_w <= rptr_gray;
            rptr_gray_sync2_w <= rptr_gray_sync1_w;
        end
    end

    // FULL 判斷：wptr_gray 與同步後的 rptr_gray 比較
    // FIFO 滿的條件（Gray Code）：
    //   MSB 和次高位相反，其餘 bits 相同
    assign WFULL = (wptr_gray == {~rptr_gray_sync2_w[ADDR_WIDTH:ADDR_WIDTH-1],
                                   rptr_gray_sync2_w[ADDR_WIDTH-2:0]});

    // =========================================================================
    // READ 端邏輯（RCLK domain）
    // =========================================================================

    // 讀取 SRAM（組合邏輯，無需時脈）
    assign RDATA = mem[raddr];

    // Read pointer 遞增
    always @(posedge RCLK or negedge RRST_N) begin
        if (!RRST_N) begin
            rptr_bin  <= 0;
            rptr_gray <= 0;
        end else if (RINC && !REMPTY) begin
            rptr_bin  <= rptr_bin + 1'b1;
            rptr_gray <= bin2gray(rptr_bin + 1'b1);
        end
    end

    // wptr_gray 同步到 RCLK domain（Two-FF Synchronizer）
    always @(posedge RCLK or negedge RRST_N) begin
        if (!RRST_N) begin
            wptr_gray_sync1_r <= 0;
            wptr_gray_sync2_r <= 0;
        end else begin
            wptr_gray_sync1_r <= wptr_gray;
            wptr_gray_sync2_r <= wptr_gray_sync1_r;
        end
    end

    // EMPTY 判斷：rptr_gray == 同步後的 wptr_gray
    assign REMPTY = (rptr_gray == wptr_gray_sync2_r);

    // =========================================================================
    // 工具函數：二進位轉 Gray Code
    // =========================================================================
    function automatic [ADDR_WIDTH:0] bin2gray;
        input [ADDR_WIDTH:0] bin;
        bin2gray = bin ^ (bin >> 1);
    endfunction

endmodule
