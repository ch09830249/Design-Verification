`ifndef AXI_DEFINE_SVH
`define AXI_DEFINE_SVH

`define D_DATA_WIDTH    32
`define D_ADDR_WIDTH    32
`define D_MEM_SIZE      4096   // words
`define D_ID_WIDTH      4

// BRESP / RRESP
`define BRESP_OKAY      2'b00
`define BRESP_EXOKAY    2'b01
`define BRESP_SLVERR    2'b10
`define BRESP_DECERR    2'b11

`define RRESP_OKAY      2'b00
`define RRESP_EXOKAY    2'b01
`define RRESP_SLVERR    2'b10
`define RRESP_DECERR    2'b11

// AWBURST / ARBURST
`define BURST_FIXED     2'b00
`define BURST_INCR      2'b01
`define BURST_WRAP      2'b10

`endif
