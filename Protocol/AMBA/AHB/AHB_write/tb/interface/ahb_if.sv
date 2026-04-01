interface ahb_if(input logic HCLK, input logic HRESETn);
  logic [31:0] HADDR;
  logic [1:0]  HTRANS;
  logic        HWRITE;
  logic [2:0]  HSIZE;
  logic [31:0] HWDATA;
  logic [31:0] HRDATA;
  logic        HREADY;
  logic        HRESP;

  // Clocking block for UVM
  clocking cb @(posedge HCLK);
    default input #1 output #1;
    output HADDR, HTRANS, HWRITE, HSIZE, HWDATA;
    input  HRDATA, HREADY, HRESP;
  endclocking

endinterface
