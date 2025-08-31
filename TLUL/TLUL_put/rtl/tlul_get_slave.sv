module tlul_get_slave (
  input  logic        clk,
  input  logic        rst_n,

  // A channel (request)
  input  logic        a_valid,
  output logic        a_ready,
  input  logic [2:0]  a_opcode,
  input  logic [2:0]  a_param,
  input  logic [3:0]  a_size,
  input  logic [3:0]  a_mask,
  input  logic [31:0] a_address,
  input  logic [31:0] a_data,
  input  logic [2:0]  a_source,

  // D channel (response)
  output logic        d_valid,
  input  logic        d_ready,
  output logic [2:0]  d_opcode,
  output logic [2:0]  d_param,
  output logic [3:0]  d_size,
  output logic [31:0] d_data,
  output logic [2:0]  d_source,
  output logic [1:0]  d_sink
);

  typedef logic [31:0] mem_t;
  mem_t mem [0:255];

  // internal registers for response
  logic [31:0] rdata_reg;
  logic [2:0]  r_source;
  logic        resp_pending;

  assign a_ready = !resp_pending;
  assign d_valid = resp_pending;
  assign d_opcode = 4;        // Get response opcode
  assign d_param  = 0;
  assign d_size   = 4;        // fixed 4 bytes response
  assign d_data   = rdata_reg;
  assign d_source = r_source;
  assign d_sink   = 0;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      resp_pending <= 0;
      rdata_reg    <= 0;
      r_source     <= 0;
    end 
    else begin
      if (!resp_pending) begin  // a_ready 拉起, d_valid 拉下
        // 接收 Get 請求
        if (a_valid && a_ready && a_opcode == 4) begin
          // 這裡加個 mask 功能
          logic [31:0] masked_data;
          masked_data = 32'h1A2B3C4F;       // 回傳的 data pattern 固定 32'h1A2B3C4F
          // 根據 a_mask 清掉不需要的 byte
          masked_data[7:0]   = a_mask[0] ? masked_data[7:0]   : 8'h00;
          masked_data[15:8]  = a_mask[1] ? masked_data[15:8]  : 8'h00;
          masked_data[23:16] = a_mask[2] ? masked_data[23:16] : 8'h00;
          masked_data[31:24] = a_mask[3] ? masked_data[31:24] : 8'h00;

          rdata_reg    <= masked_data;
          r_source     <= a_source;
          resp_pending <= 1;            // a_ready 拉下, d_valid 拉起
        end
      end 
      else begin
        // 回應完成
        if (d_valid && d_ready) begin   // d_ready 拉起代表 master 已收資料
          resp_pending <= 0;
        end
      end
    end
  end
endmodule
