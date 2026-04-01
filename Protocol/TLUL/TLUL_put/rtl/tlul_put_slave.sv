module tlul_put_slave #(
    parameter int AW = 32,  // address width
    parameter int DW = 32   // data width
)(
    input  logic           clk,
    input  logic           rst_n,

    // TL-UL a channel (request)
    input  logic           a_valid,
    output logic           a_ready,
    input  logic  [2:0]    a_opcode,   // 0: PutFullData, 1: PutPartialData
    input  logic  [2:0]    a_param,
    input  logic  [3:0]    a_size,
    input  logic  [3:0]    a_mask,
    input  logic  [AW-1:0] a_address,
    input  logic  [DW-1:0] a_data,
    input  logic  [2:0]    a_source,

    // TL-UL d channel (response)
    output logic           d_valid,
    input  logic           d_ready,
    output logic  [1:0]    d_opcode,     // 0: AccessAck
    output logic  [2:0]    d_param,
    output logic  [3:0]    d_size,
    output logic  [31:0]   d_data,
    output logic  [2:0]    d_source,
    output logic  [1:0]    d_sink
);

  // Simple memory: 1KB (adjustable)
  logic [7:0] mem [0:1023];

  // internal handshake signals
  logic request_accepted;
  logic        resp_pending;
  logic [AW-1:0] addr_reg;
  logic [DW-1:0] data_reg;        // for debug
  logic [3:0]    mask_reg;
  logic [DW-1:0] masked_data;

  assign a_ready = 1'b1;  // always ready to accept
  assign d_opcode = 2'b00; // AccessAck
  assign request_accepted = a_valid && a_ready;
  assign d_param  = 0;
  assign d_source = a_source;
  assign d_sink   = 0;

  // Save transaction
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      resp_pending <= 1'b0;
    end 
    else if (request_accepted) begin
      addr_reg <= a_address;
      mask_reg <= a_mask;
      resp_pending <= 1'b1;

      // Do memory write
      if (a_opcode == 1) begin       // PutPartial
        // Mask each byte of a_data with corresponding a_mask bit
        for (int i = 0; i < 4; i++) begin
          mem[a_address][8*i +: 8] <= a_mask[i] ? a_data[8*i +: 8] : 8'h00;     // a_data[8*i +: 8] 代表從位元 8*i 開始的 8 bits
          data_reg[8*i +: 8]       <= a_mask[i] ? a_data[8*i +: 8] : 8'h00;
        end
      end
      else if (a_opcode == 0) begin  // PutFull
        mem[a_address] <= a_data;
        data_reg       <= a_data;
      end
    end 
    else if (d_valid && d_ready) begin
      resp_pending <= 1'b0;
    end
  end

  assign d_valid = resp_pending;

endmodule
