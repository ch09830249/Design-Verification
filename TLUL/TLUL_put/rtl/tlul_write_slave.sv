module ahb_write_slavel (
  input  logic         HCLK,
  input  logic         HRESETn,
  input  logic         HSEL,
  input  logic         HWRITE,
  input  logic [1:0]   HTRANS,
  input  logic [31:0]  HADDR,
  input  logic [31:0]  HWDATA,
  output logic         HREADYOUT
);

  logic [31:0] mem [0:255];

  assign HREADYOUT = 1;

  always_ff @(posedge HCLK or negedge HRESETn) begin
    if (!HRESETn) begin
      int i;
      for (i = 0; i < 256; i++)
        mem[i] <= 0;
    end else begin
      if (HSEL && HWRITE && HTRANS[1]) begin
        mem[HADDR[9:2]] <= HWDATA;
      end
    end
  end

endmodule
