module counter (
  input  logic       clk,
  input  logic       rst_n,
  input  logic       en,
  output logic [3:0] count
);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      count <= 0;
    else if (en)
      count <= count + 1;
  end

endmodule