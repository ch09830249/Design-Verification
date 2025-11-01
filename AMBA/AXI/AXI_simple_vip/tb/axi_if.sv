// 支援完整 AXI4 寫入與讀取通道，包括 burst、lock、QoS 訊號
interface axi_if #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4,
    parameter USER_WIDTH = 4
)(
    input logic ACLK,
    input logic ARESETn
);

    // Write address channel
    logic [ID_WIDTH-1:0]     AWID;
    logic [ADDR_WIDTH-1:0]   AWADDR;
    logic [7:0]              AWLEN;
    logic [2:0]              AWSIZE;
    logic [1:0]              AWBURST;
    logic                    AWLOCK;
    logic [3:0]              AWCACHE;
    logic [2:0]              AWPROT;
    logic [3:0]              AWQOS;
    logic                    AWVALID;
    logic                    AWREADY;

    // Write data channel
    logic [DATA_WIDTH-1:0]   WDATA;
    logic [(DATA_WIDTH/8)-1:0] WSTRB;
    logic                    WLAST;
    logic                    WVALID;
    logic                    WREADY;

    // Write response channel
    logic [ID_WIDTH-1:0]     BID;
    logic [1:0]              BRESP;
    logic                    BVALID;
    logic                    BREADY;

    // Read address channel
    logic [ID_WIDTH-1:0]     ARID;
    logic [ADDR_WIDTH-1:0]   ARADDR;
    logic [7:0]              ARLEN;
    logic [2:0]              ARSIZE;
    logic [1:0]              ARBURST;
    logic                    ARLOCK;
    logic [3:0]              ARCACHE;
    logic [2:0]              ARPROT;
    logic [3:0]              ARQOS;
    logic                    ARVALID;
    logic                    ARREADY;

    // Read data channel
    logic [ID_WIDTH-1:0]     RID;
    logic [DATA_WIDTH-1:0]   RDATA;
    logic [1:0]              RRESP;
    logic                    RLAST;
    logic                    RVALID;
    logic                    RREADY;

endinterface
