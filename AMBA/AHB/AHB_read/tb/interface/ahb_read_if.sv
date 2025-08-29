interface ahb_if(input logic HCLK, input logic HRESETn);

  logic [31:0] HADDR;
  logic [31:0] HWDATA;
  logic        HWRITE;
  logic [1:0]  HTRANS;
  logic        HREADY;
  logic        HREADYOUT;
  logic        HSEL;

endinterface
