module apb_read_slave #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32,
    parameter MEM_DEPTH  = 256
)(
    input  wire                   PCLK,
    input  wire                   PRESETn,
    input  wire                   PSEL,
    input  wire                   PENABLE,
    input  wire                   PWRITE,
    input  wire [ADDR_WIDTH-1:0]  PADDR,
    output reg  [DATA_WIDTH-1:0]  PRDATA,
    output reg                    PREADY
);

    // Internal memory for storing read data
    // Default: 256 x 32-bit memory
    reg [DATA_WIDTH-1:0] mem [0:MEM_DEPTH-1];

    // Initialization (optional)
    integer i;
    initial begin
        for (i = 0; i < MEM_DEPTH; i = i + 1) begin
            mem[i] = 32'hA5A50000 + i;  // Pattern data: 32'hA5A50000, 32'hA5A50001, 32'hA5A50002...
        end
    end

    // Read logic
    always @(posedge PCLK or negedge PRESETn) begin
        // Reset
        if (!PRESETn) begin
            PREADY <= 0;
            PRDATA <= 0;
        end 
        else begin
            if (PSEL && PENABLE && !PWRITE) begin
                PREADY <= 1;
                PRDATA <= mem[PADDR[ADDR_WIDTH-1:2]]; // Word aligned (4 bytes)
            end else begin
                PREADY <= 0;
                PRDATA <= 0;
            end
        end
    end

endmodule
