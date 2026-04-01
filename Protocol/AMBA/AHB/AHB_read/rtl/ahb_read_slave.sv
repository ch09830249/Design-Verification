module ahb_read_slave(
  input logic HCLK,
  input logic HRESETn,
  input logic [31:0] HADDR,
  input logic [1:0]  HTRANS,
  input logic        HWRITE,
  input logic [2:0]  HSIZE,
  input logic [31:0] HWDATA,
  output logic [31:0] HRDATA,
  output logic        HREADY,
  output logic        HRESP
);
  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
      HRDATA <= 0;
      HREADY <= 1;
      HRESP  <= 0;
    end else begin
      if (HTRANS == 2'b10 && !HWRITE) begin
        HRDATA <= HADDR + 32'h0000_A5A5; // Dummy data
      end
      HREADY <= 1;
      HRESP  <= 0;
    end
  end
endmodule
