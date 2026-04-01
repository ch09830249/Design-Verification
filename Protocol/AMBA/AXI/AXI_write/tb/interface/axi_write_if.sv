interface axi_write_if(input logic ACLK, input logic ARESETn);
  logic [31:0] AWADDR;
  logic        AWVALID, AWREADY;
  logic [31:0] WDATA;
  logic        WVALID, WREADY;
  logic [1:0]  BRESP;
  logic        BVALID, BREADY;
endinterface
