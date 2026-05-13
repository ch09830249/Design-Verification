module apb_memory_slave #(
    parameter ADDR_WIDTH = 10,     // 記憶體深度為 2^10 = 1024 words (4 bytes)
    parameter DATA_WIDTH = 32,
    parameter WAIT_CYCLES = 0      // 可設定等待週期，用來練 VIP 的 PREADY 處理
)(
    input  wire                   PCLK,
    input  wire                   PRESETn,

    // APB 介面
    input  wire [31:0]            PADDR,
    input  wire                   PSEL,
    input  wire                   PENABLE,
    input  wire                   PWRITE,
    input  wire [DATA_WIDTH-1:0]  PWDATA,
    input  wire [(DATA_WIDTH/8)-1:0] PSTRB, // APB4 寫入選通
    output reg  [DATA_WIDTH-1:0]  PRDATA,
    output wire                   PREADY,
    output wire                   PSLVERR
);

    // 內部存儲器定義
    reg [DATA_WIDTH-1:0] mem [0:(2**ADDR_WIDTH)-1];

    // 內部狀態與計數器（用於模擬等待週期）
    reg [3:0] wait_cnt;
    wire      is_access = PSEL && PENABLE;

    // --- PREADY 控制邏輯 ---
    // 如果 WAIT_CYCLES > 0，則 PREADY 會延遲拉高
    assign PREADY = (wait_cnt == WAIT_CYCLES);
    assign PSLVERR = 1'b0; // 暫不模擬錯誤情形

    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            wait_cnt <= 4'd0;
        end else if (PSEL && !PENABLE) begin
            // Setup 階段，重置計數器
            wait_cnt <= 4'd0;
        end else if (is_access && !PREADY) begin
            // Access 階段，如果還沒準備好就累加
            wait_cnt <= wait_cnt + 1'b1;
        end
    end

    // --- 寫入邏輯 (支援 PSTRB) ---
    integer i;
    always @(posedge PCLK) begin
        if (is_access && PWRITE && PREADY) begin
            for (i = 0; i < (DATA_WIDTH/8); i = i + 1) begin
                if (PSTRB[i]) begin
                    // 根據 Byte Strobe 寫入對應的 8-bit
                    mem[PADDR[ADDR_WIDTH+1:2]][(i*8) +: 8] <= PWDATA[(i*8) +: 8];
                end
            end
        end
    end

    // --- 讀取邏輯 ---
    always @(posedge PCLK or negedge PRESETn) begin
        if (!PRESETn) begin
            PRDATA <= {DATA_WIDTH{1'b0}};
        end else if (PSEL && !PWRITE && !PENABLE) begin
            // 在 Setup 階段就先準備好數據 (符合 APB 低功耗讀取建議)
            PRDATA <= mem[PADDR[ADDR_WIDTH+1:2]];
        end
    end

endmodule