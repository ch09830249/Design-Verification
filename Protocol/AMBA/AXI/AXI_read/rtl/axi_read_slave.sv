module axi_read_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input  logic                 ACLK,
    input  logic                 ARESETn,

    input  logic [ADDR_WIDTH-1:0] ARADDR,
    input  logic                  ARVALID,
    output logic                  ARREADY,

    output logic [DATA_WIDTH-1:0] RDATA,
    output logic [1:0]            RRESP,
    output logic                  RVALID,
    input  logic                  RREADY
);

    typedef enum logic [1:0] {
        R_IDLE, R_ADDR_ACCEPTED, R_RESP_SENT
    } r_state_t;

    r_state_t rstate;

    always_ff @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            ARREADY <= 0;
            RVALID  <= 0;
            RRESP   <= 2'b00;
            RDATA   <= 0;
            rstate  <= R_IDLE;
        end 
        else begin
            case (rstate)
                R_IDLE: begin
                    if (ARVALID) begin
                        ARREADY <= 1;
                        rstate <= R_ADDR_ACCEPTED;
                    end
                end

                R_ADDR_ACCEPTED: begin
                    ARREADY <= 0;
                    RVALID <= 1;
                    RRESP  <= 2'b00;
                    /*
                        回傳資料為: 前 16 bits 為 ABCD, 後 16 bits 為 Read address bit 15~0
                    */
                    RDATA  <= {16'hABCD, ARADDR[15:0]};
                    rstate <= R_RESP_SENT;
                end

                R_RESP_SENT: begin
                    if (RREADY) begin
                        RVALID <= 0;
                        rstate <= R_IDLE;
                    end
                end
            endcase
        end
    end

endmodule
