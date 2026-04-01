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

    // 尚未使用到
    // =======================
    // Clocking blocks
    // =======================
    clocking cb_wr @(posedge ACLK);
        input  AWREADY, WREADY, BVALID;
        output AWVALID, AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS;
        output WVALID, WDATA, WSTRB, WLAST;
        output BREADY;
    endclocking

    clocking cb_rd @(posedge ACLK);
        input  ARREADY, RVALID, RDATA, RRESP, RLAST;
        output ARVALID, ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS;
        output RREADY;
    endclocking

    // =======================
    // Modports
    // =======================
    // Master writes
    modport master_wr (
        input  AWREADY, WREADY, BVALID,
        output AWVALID, AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS,
        output WVALID, WDATA, WSTRB, WLAST,
        output BREADY
    );

    // Master reads
    modport master_rd (
        input  ARREADY, RVALID, RDATA, RRESP, RLAST,
        output ARVALID, ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS,
        output RREADY
    );

    // Slave interface (input = master output, output = master input)
    modport slave_wr (
        input  AWVALID, AWID, AWADDR, AWLEN, AWSIZE, AWBURST, AWLOCK, AWCACHE, AWPROT, AWQOS,
        input  WVALID, WDATA, WSTRB, WLAST,
        input  BREADY,
        output AWREADY, WREADY, BVALID
    );

    modport slave_rd (
        input  ARVALID, ARID, ARADDR, ARLEN, ARSIZE, ARBURST, ARLOCK, ARCACHE, ARPROT, ARQOS,
        input  RREADY,
        output ARREADY, RVALID, RDATA, RRESP, RLAST
    );

    /*
        Clocking blocks (cb_wr, cb_rd)
            包含主動抓取（input）和主動驅動（output）訊號
            在 driver/monitor 裡可以直接用 @cb_wr / @cb_rd 同步觸發
        Modports
            master_wr / master_rd → master 使用
            slave_wr / slave_rd → slave 使用
            保證訊號方向正確，方便在 UVM driver/monitor 中直接綁定 virtual interface
    */

endinterface
