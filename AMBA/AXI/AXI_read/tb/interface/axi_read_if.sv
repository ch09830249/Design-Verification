interface axi_read_if(input logic ACLK, input logic ARESETn);
    logic [31:0] ARADDR;
    logic        ARVALID;
    logic        ARREADY;
    logic [31:0] RDATA;
    logic [1:0]  RRESP;
    logic        RVALID;
    logic        RREADY;
endinterface
