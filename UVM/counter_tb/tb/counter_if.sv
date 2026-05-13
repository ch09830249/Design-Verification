interface counter_if (input logic clk);
    logic        rst_n;
    logic        reverse;
    logic [31:0] min_val;
    logic [31:0] max_val;
    logic [31:0] count;
    logic        direction;
endinterface : counter_if
