module apb_write_slave (
  input logic         PCLK,
  input logic         PRESETn,
  input logic         PSEL,
  input logic         PENABLE,
  input logic         PWRITE,
  input logic [31:0]  PADDR,
  input logic [31:0]  PWDATA,
  output logic        PREADY
);

  // 256 x 32-bit memory
  logic [31:0] mem [0:255];

  // Simple ready signal (always ready)
  assign PREADY = 1;

  always_ff @(posedge PCLK or negedge PRESETn) begin
    if (!PRESETn) begin
      // Optional reset behavior
      int i;
      for (i = 0; i < 256; i++) begin
        mem[i] <= 32'h0;
      end
    end else begin
      if (PSEL && PENABLE && PWRITE) begin
        // Memory write
        mem[PADDR[9:2]] <= PWDATA; // Assume word-aligned (4-byte)
      end
    end
  end

endmodule
