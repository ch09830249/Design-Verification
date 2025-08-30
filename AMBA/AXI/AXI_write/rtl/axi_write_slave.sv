module axi_write_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input  logic                 ACLK,
    input  logic                 ARESETn,

    // Write address channel
    input  logic [ADDR_WIDTH-1:0] AWADDR,
    input  logic                  AWVALID,
    output logic                  AWREADY,

    // Write data channel
    input  logic [DATA_WIDTH-1:0] WDATA,
    input  logic                  WVALID,
    output logic                  WREADY,

    // Write response channel
    output logic [1:0]            BRESP,
    output logic                  BVALID,
    input  logic                  BREADY
);

    typedef enum logic [1:0] {
        IDLE, ADDR_ACCEPTED, DATA_ACCEPTED, RESP_SENT
    } state_t;

    state_t state;

    logic [ADDR_WIDTH-1:0] write_addr;
    logic [DATA_WIDTH-1:0] write_data;

    always_ff @(posedge ACLK or negedge ARESETn) begin
        if (!ARESETn) begin
            AWREADY <= 0;
            WREADY  <= 0;
            BVALID  <= 0;
            BRESP   <= 2'b00;
            state   <= IDLE;
        end 
        else begin
            case (state)
                IDLE: begin
                    if (AWVALID) begin
                        AWREADY <= 1;
                        write_addr <= AWADDR;
                        state <= ADDR_ACCEPTED;
                    end
                end

                ADDR_ACCEPTED: begin
                    AWREADY <= 0;
                    if (WVALID) begin
                        WREADY <= 1;
                        write_data <= WDATA;
                        state <= DATA_ACCEPTED;
                    end
                end

                DATA_ACCEPTED: begin
                    WREADY <= 0;
                    BVALID <= 1;
                    BRESP  <= 2'b00; // 不管寫甚麼都回傳 OKAY
                    state <= RESP_SENT;
                end

                RESP_SENT: begin
                    if (BREADY) begin
                        BVALID <= 0;
                        state <= IDLE;
                    end
                end
            endcase
        end
    end

endmodule
s
