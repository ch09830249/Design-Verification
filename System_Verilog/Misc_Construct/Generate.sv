/*
 SystemVerilog 中，generate 是一種 建構時期（compile-time） 的機制，用來：
   - 根據參數、常數條件，決定要產生哪些硬體結構
   - 自動產生重複的邏輯或模組例化（instance）
  它不會在模擬時發生，而是在模擬或綜合之前，先「攤平」你的程式碼。

  你可以：

   - 做迴圈產生多個模組 / 訊號 / 寄存器
   - 根據條件（像是 if）選擇產生不同邏輯
   - 搭配參數（如 parameter WIDTH = 8）產生不同版本的設計
*/
generate
  // 條件、for 迴圈都可以放這
endgenerate

genvar i;

generate
  for (i = 0; i < 4; i = i + 1) begin : gen_loop
    // 建立多個模組或邏輯
  end
endgenerate

// ✅ 範例 1：重複例化模組（4 個加法器）
module top;

  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : add_gen
      adder u_adder (
        .a (in_a[i]),
        .b (in_b[i]),
        .sum (out_sum[i])
      );
    end
  endgenerate

endmodule

// ✅ 範例 2：根據參數產生不同邏輯
module mux #(parameter WIDTH = 8) (
  input logic [WIDTH-1:0] in0, in1,
  input logic sel,
  output logic [WIDTH-1:0] out
);

  generate
    if (WIDTH == 8) begin
      assign out = sel ? in1 : in0;
    end else begin
      // 用其他方式產生資料路徑
      always_comb begin
        out = sel ? in1 : in0;
      end
    end
  endgenerate

endmodule

/*
常搭配關鍵字：
關鍵字	        用途
generate	包住所有產生式語法
genvar	  建構時用的變數，只能在 generate 裡用
for	      重複產生邏輯/模組
if	      條件選擇邏輯產生
case	    根據參數選擇不同邏輯
: 名稱	  每個 generate block 命名（建議一定要命名）
*/

/*
🚨 注意事項：
1. 不能用變數（如 wire 或 reg）控制 generate 條件
   必須用 parameter 或 localparam
2. genvar 只能用在 generate 區塊內
3. 每個 generate block 要命名（這樣除錯容易）
*/

/*
目標：產生 N 個 8-bit 寄存器，每個都有自己的輸入和使能
✅ 範例程式碼：參數化寄存器陣列
📐 假設：
每個寄存器寬度為 8 bits（可調整）
1. 用 generate 自動產生 N 個
2. 支援 write enable 控制
3. 資料輸入為 data_in[N][8]
4. 寄存器輸出為 reg_out[N][8]
*/

module reg_array #(
  parameter N = 4,           // 寄存器個數
  parameter WIDTH = 8        // 每個寄存器寬度
)(
  input  logic              clk,
  input  logic [N-1:0]      we,       // 每個寄存器的 write enable
  input  logic [WIDTH-1:0]  data_in[N],
  output logic [WIDTH-1:0]  reg_out[N]
);

  genvar i;
  generate
    for (i = 0; i < N; i++) begin : reg_gen
      always_ff @(posedge clk) begin
        if (we[i])
          reg_out[i] <= data_in[i];
      end
    end
  endgenerate

endmodule

module top;

  logic clk;
  logic [3:0] we;
  logic [7:0] data_in[4];
  logic [7:0] reg_out[4];

  reg_array #(.N(4), .WIDTH(8)) u_regs (
    .clk(clk),
    .we(we),
    .data_in(data_in),
    .reg_out(reg_out)
  );

  // 產生時脈 & 測試寫入可以放在 initial block 裡
endmodule