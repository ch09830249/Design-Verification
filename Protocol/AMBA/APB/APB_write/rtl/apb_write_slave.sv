// module apb_write_slave (
//   input logic         PCLK,
//   input logic         PRESETn,
//   input logic         PSEL,
//   input logic         PENABLE,
//   input logic         PWRITE,
//   input logic [31:0]  PADDR,
//   input logic [31:0]  PWDATA,
//   output logic        PREADY
// );

//   // 256 x 32-bit memory
//   logic [31:0] mem [0:255];

//   // Simple ready signal (always ready) => 這裡是無時無刻都可以收資料的版本
//   assign PREADY = 1;

//   always_ff @(posedge PCLK or negedge PRESETn) begin
//     if (!PRESETn) begin
//       // Optional reset behavior => 將 mem 全部清 0
//       int i;
//       for (i = 0; i < 256; i++) begin
//         mem[i] <= 32'h0;
//       end
//     end 
//     else begin
//       if (PSEL && PENABLE && PWRITE) begin
//         // Memory write
//         mem[PADDR[9:2]] <= PWDATA; // Assume word-aligned (4-byte) => 9 是因為最大就 255, 2 是因為 word aligned
//       end
//     end
//   end

// endmodule

module apb_write_slave (
  input  logic         PCLK,
  input  logic         PRESETn,
  input  logic         PSEL,
  input  logic         PENABLE,
  input  logic         PWRITE,
  input  logic [31:0]  PADDR,
  input  logic [31:0]  PWDATA,
  output logic         PREADY
);

  // Internal memory for storing write data
  // 256 x 32-bit memory
  logic [31:0] mem [0:255];

  // Ready delay counter
  logic [1:0] wait_cnt;
  logic       ready_next;

  always_ff @(posedge PCLK or negedge PRESETn) begin
    // Reset
    if (!PRESETn) begin
      int i;
      for (i = 0; i < 256; i++) begin
        mem[i] <= 32'h0;                // mem 清 0
      end
      wait_cnt   <= 0;                  // wait_cnt 重新累積
      PREADY     <= 0;
      ready_next <= 0;
    end 
    else begin
      // [等待狀態] 2 個 posedge 後才可以舉 PREADY 收 write data
      if (PSEL && PENABLE && !PREADY) begin
        wait_cnt <= wait_cnt + 1;
        if (wait_cnt == 2) begin
          PREADY     <= 1;
          ready_next <= 1;    // 此 flag 代表下個 clk 可以收 write data 了
        end else begin
          PREADY <= 0;        // 還未等 2 個 posedge (PSEL && PENABLE && !PREADY)
        end
      end
      // [完成等待寫入並回到 idle]
      else if (PREADY && ready_next) begin
        if (PWRITE) begin
          mem[PADDR[9:2]] <= PWDATA;
        end
        wait_cnt   <= 0;
        PREADY     <= 0;
        ready_next <= 0;
      end 
      // [其他狀況 PREADY 都必須為 0]
      else begin
        PREADY <= 0;
      end
    end
  end

endmodule

/*
  改成：PREADY 兩個週期後才拉高完成傳輸
    行為階段	                          描述
    PSEL &&                 PENABLE	偵測到傳輸開始，開始計數
  wait_cnt == 2	            過了兩個時鐘後將 PREADY 拉高
    PREADY == 1	                寫入資料並清除計數器
    傳輸結束後	                回到 idle，等待下次寫入
*/
