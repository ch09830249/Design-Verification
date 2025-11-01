module axi_slave_dut #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32,
    parameter ID_WIDTH   = 4
)(
    input  logic ACLK,
    input  logic ARESETn,

    // Write address channel
    input  logic [ID_WIDTH-1:0]    AWID,
    input  logic [ADDR_WIDTH-1:0]  AWADDR,
    input  logic [7:0]             AWLEN,
    input  logic [2:0]             AWSIZE,
    input  logic [1:0]             AWBURST,
    input  logic                   AWLOCK,
    input  logic [3:0]             AWCACHE,
    input  logic [2:0]             AWPROT,
    input  logic [3:0]             AWQOS,
    input  logic                   AWVALID,
    output logic                   AWREADY,

    // Write data channel
    input  logic [DATA_WIDTH-1:0]  WDATA,
    input  logic [(DATA_WIDTH/8)-1:0] WSTRB,
    input  logic                   WLAST,
    input  logic                   WVALID,
    output logic                   WREADY,

    // Write response channel
    output logic [ID_WIDTH-1:0]    BID,
    output logic [1:0]             BRESP,
    output logic                   BVALID,
    input  logic                   BREADY,

    // Read address channel
    input  logic [ID_WIDTH-1:0]    ARID,
    input  logic [ADDR_WIDTH-1:0]  ARADDR,
    input  logic [7:0]             ARLEN,
    input  logic [2:0]             ARSIZE,
    input  logic [1:0]             ARBURST,
    input  logic                   ARLOCK,
    input  logic [3:0]             ARCACHE,
    input  logic [2:0]             ARPROT,
    input  logic [3:0]             ARQOS,
    input  logic                   ARVALID,
    output logic                   ARREADY,

    // Read data channel
    output logic [ID_WIDTH-1:0]    RID,
    output logic [DATA_WIDTH-1:0]  RDATA,
    output logic [1:0]             RRESP,
    output logic                   RLAST,
    output logic                   RVALID,
    input  logic                   RREADY
);

    // ----------------------------
    // Internal memory (1K words)
    // ----------------------------
    localparam MEM_DEPTH = 1024;
    logic [DATA_WIDTH-1:0] mem[0:MEM_DEPTH-1];
    logic [DATA_WIDTH-1:0] debug_mem;

    // ----------------------------
    // Write logic
    // ----------------------------
    typedef enum logic [2:0] {
        W_IDLE, W_DATA, W_RESP_SENT
    } wstate_t;

    wstate_t wstate;
    logic [ADDR_WIDTH-1:0] waddr;
    logic [7:0]            wburst_cnt;
    logic [ID_WIDTH-1:0]   wid_reg;

    // ----------------------------
    // Read logic
    // ----------------------------
    typedef enum logic [2:0] {
        R_IDLE, R_ADDR_ACCEPTED, R_DATA_RESP_SENT
    } rstate_t;

    rstate_t rstate;
    logic [ADDR_WIDTH-1:0] raddr;
    logic [7:0]            rburst_cnt;
    logic [ID_WIDTH-1:0]   rid_reg;

    // ----------------------------
    // Reset logic
    // ----------------------------
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            // Write
            wstate     <= W_IDLE;
            AWREADY    <= 1;
            WREADY     <= 0;
            BVALID     <= 0;

            // Read
            rstate     <= R_IDLE;
            ARREADY    <= 1;
            RVALID     <= 0;
            RLAST      <= 0;
        end else begin

            // ----------------------------
            // Write channel FSM
            // ----------------------------
            case (wstate)
                W_IDLE: begin
                    if (AWVALID) begin
                        waddr       <= AWADDR;
                        wid_reg     <= AWID;
                        wburst_cnt  <= AWLEN;
                        AWREADY     <= 0;
                        WREADY      <= 1;
                        wstate      <= W_DATA;
                    end
                end

                W_DATA: begin
                    if (WVALID) begin
                        // Byte write with WSTRB
                        for (int i = 0; i < DATA_WIDTH/8; i++) begin
                            if (WSTRB[i]) begin
                                debug_mem[8*i +: 8] <= WDATA[8*i +: 8];
                            end else begin
                                debug_mem[8*i +: 8] <= 8'h00;
                            end
                        end
                        waddr <= waddr + 4;

                        if (WLAST || (wburst_cnt == 0)) begin
                            BRESP  <= 2'b00;  // OKAY
                            BID    <= wid_reg;
                            BVALID <= 1;
                            wstate <= W_RESP_SENT;
                        end else begin
                            wburst_cnt <= wburst_cnt - 1;
                        end
                    end
                end

                W_RESP_SENT: begin
                    if (BREADY) begin
                        BVALID <= 0;
                        AWREADY <= 1;
                        wstate <= W_IDLE;
                    end
                end
            endcase

            // ----------------------------
            // Read channel FSM
            // ----------------------------
            case (rstate)
                R_IDLE: begin
                    if (ARVALID) begin
                        raddr       <= ARADDR;
                        rid_reg     <= ARID;
                        rburst_cnt  <= ARLEN;
                        ARREADY     <= 0;
                        rstate      <= R_DATA_RESP_SENT;
                    end
                end

                R_DATA_RESP_SENT: begin
                    if (RREADY) begin
                        if (RLAST) begin
                            RVALID  <= 0;
                            RLAST   <= 0;
                            rstate  <= R_IDLE;
                        end else begin
                            raddr      <= raddr + 4;
                            rburst_cnt <= rburst_cnt - 1;
                            RDATA      <= mem[(raddr + 4) >> 2];
                            RVALID     <= 1;
                            RLAST      <= (rburst_cnt == 1);
                        end
                    end
                end
            endcase

        end
    end

endmodule
