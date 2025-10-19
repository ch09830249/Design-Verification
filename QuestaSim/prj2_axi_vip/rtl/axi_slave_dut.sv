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

    // ----------------------------
    // Write logic
    // ----------------------------
    typedef enum logic [1:0] {
        W_IDLE, W_DATA, W_RESP
    } wstate_t;

    wstate_t wstate;
    logic [ADDR_WIDTH-1:0] waddr;
    logic [7:0]            wburst_cnt;
    logic [ID_WIDTH-1:0]   wid_reg;

    // ----------------------------
    // Read logic
    // ----------------------------
    typedef enum logic [1:0] {
        R_IDLE, R_DATA_STATE
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
            AWREADY    <= 0;
            WREADY     <= 0;
            BVALID     <= 0;
            BRESP      <= 2'b00;
            BID        <= 0;

            // Read
            ARREADY    <= 0;
            RVALID     <= 0;
            RLAST      <= 0;
            RRESP      <= 2'b00;
            RID        <= 0;
            RDATA      <= 0;
        end else begin

            // ----------------------------
            // Write channel FSM
            // ----------------------------
            case (wstate)
                W_IDLE: begin
                    AWREADY <= 1;
                    if (AWVALID) begin
                        waddr      <= AWADDR;
                        wid_reg    <= AWID;
                        wburst_cnt <= AWLEN;
                        AWREADY    <= 0;
                        WREADY     <= 1;
                        wstate     <= W_DATA;
                    end
                end

                W_DATA: begin
                    if (WVALID) begin
                        // Byte write with WSTRB
                        for (int i = 0; i < DATA_WIDTH/8; i++) begin
                            if (WSTRB[i]) begin
                                mem[waddr[11:2]][8*i +: 8] <= WDATA[8*i +: 8];
                            end
                        end
                        waddr <= waddr + 4;

                        if (WLAST || (wburst_cnt == 0)) begin
                            WREADY <= 0;
                            BVALID <= 1;
                            BRESP  <= 2'b00;  // OKAY
                            BID    <= wid_reg;
                            wstate <= W_RESP;
                        end else begin
                            wburst_cnt <= wburst_cnt - 1;
                        end
                    end
                end

                W_RESP: begin
                    if (BREADY) begin
                        BVALID <= 0;
                        wstate <= W_IDLE;
                    end
                end
            endcase

            // ----------------------------
            // Read channel FSM
            // ----------------------------
            case (rstate)
                R_IDLE: begin
                    ARREADY <= 1;
                    if (ARVALID) begin
                        raddr      <= ARADDR;
                        rburst_cnt <= ARLEN;
                        rid_reg    <= ARID;
                        ARREADY    <= 0;
                        RVALID     <= 1;
                        RID        <= ARID;
                        RDATA      <= mem[ARADDR[11:2]];
                        RLAST      <= (ARLEN == 0);
                        rstate     <= R_DATA_STATE;
                    end
                end

                R_DATA_STATE: begin
                    if (RVALID && RREADY) begin
                        if (RLAST) begin
                            RVALID  <= 0;
                            RLAST   <= 0;
                            rstate  <= R_IDLE;
                        end else begin
                            raddr      <= raddr + 4;
                            rburst_cnt <= rburst_cnt - 1;
                            RDATA      <= mem[(raddr + 4) >> 2];
                            RLAST      <= (rburst_cnt == 1);
                        end
                    end
                end
            endcase

        end
    end

endmodule
