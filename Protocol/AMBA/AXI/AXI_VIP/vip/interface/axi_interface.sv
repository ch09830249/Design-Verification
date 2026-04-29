`ifndef AXI_INTERFACE_SV
`define AXI_INTERFACE_SV

`include "axi_define.svh"

interface axi_interface;

    logic                           ACLK;
    logic                           ARESETn;

    // ---- AW channel (Write Address) ----
    logic [`D_ID_WIDTH-1:0]         AWID;
    logic [`D_ADDR_WIDTH-1:0]       AWADDR;
    logic [7:0]                     AWLEN;
    logic [2:0]                     AWSIZE;
    logic [1:0]                     AWBURST;
    logic                           AWVALID;
    logic                           AWREADY;

    // ---- W channel (Write Data) ----
    logic [`D_DATA_WIDTH-1:0]       WDATA;
    logic [`D_DATA_WIDTH/8-1:0]     WSTRB;
    logic                           WLAST;
    logic                           WVALID;
    logic                           WREADY;

    // ---- B channel (Write Response) ----
    logic [`D_ID_WIDTH-1:0]         BID;
    logic [1:0]                     BRESP;
    logic                           BVALID;
    logic                           BREADY;

    // ---- AR channel (Read Address) ----
    logic [`D_ID_WIDTH-1:0]         ARID;
    logic [`D_ADDR_WIDTH-1:0]       ARADDR;
    logic [7:0]                     ARLEN;
    logic [2:0]                     ARSIZE;
    logic [1:0]                     ARBURST;
    logic                           ARVALID;
    logic                           ARREADY;

    // ---- R channel (Read Data) ----
    logic [`D_ID_WIDTH-1:0]         RID;
    logic [`D_DATA_WIDTH-1:0]       RDATA;
    logic [1:0]                     RRESP;
    logic                           RLAST;
    logic                           RVALID;
    logic                           RREADY;

    modport master (
        input   ACLK, ARESETn,
        // AW
        output  AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWVALID,
        input   AWREADY,
        // W
        output  WDATA, WSTRB, WLAST, WVALID,
        input   WREADY,
        // B
        input   BID, BRESP, BVALID,
        output  BREADY,
        // AR
        output  ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARVALID,
        input   ARREADY,
        // R
        input   RID, RDATA, RRESP, RLAST, RVALID,
        output  RREADY
    );

    modport slave (
        input   ACLK, ARESETn,
        // AW
        input   AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWVALID,
        output  AWREADY,
        // W
        input   WDATA, WSTRB, WLAST, WVALID,
        output  WREADY,
        // B
        output  BID, BRESP, BVALID,
        input   BREADY,
        // AR
        input   ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARVALID,
        output  ARREADY,
        // R
        output  RID, RDATA, RRESP, RLAST, RVALID,
        input   RREADY
    );

endinterface

`endif
