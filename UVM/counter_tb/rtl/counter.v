// =============================================================================
// File    : counter.v
// Desc    : 32-bit up/down counter with min/max boundary and reverse control
//           - Counts up:   min, min+1, ..., max, then reverses
//           - Counts down: max, max-1, ..., min, then reverses
//           - reverse==1 (single cycle pulse) toggles direction
//           - Hitting boundary auto-toggles direction
//
// Fix: count always block uses next_direction (combinational) instead of
//      the registered direction, so boundary wrap and direction flip are
//      consistent within the same clock edge.
// =============================================================================
module counter (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        reverse,          // single-cycle pulse -> toggle direction
    input  wire [31:0] min_val,          // inclusive lower boundary
    input  wire [31:0] max_val,          // inclusive upper boundary
    output reg  [31:0] count,
    output reg         direction         // 0 = up, 1 = down
);

    wire at_max = (count == max_val);
    wire at_min = (count == min_val);

    // -------------------------------------------------------------------------
    // Next-direction (combinational) – used by both always blocks
    // so count and direction always agree on the same edge
    // -------------------------------------------------------------------------
    reg next_direction;
    always @(*) begin
        if (reverse) begin
            next_direction = ~direction;
        end else if (!direction && at_max) begin
            next_direction = 1'b1;
        end else if (direction && at_min) begin
            next_direction = 1'b0;
        end else begin
            next_direction = direction;
        end
    end

    // -------------------------------------------------------------------------
    // Direction register
    // -------------------------------------------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            direction <= 1'b0;
        else
            direction <= next_direction;
    end

    // -------------------------------------------------------------------------
    // Counter – uses next_direction so the first step after a bounce
    // immediately goes the right way
    // -------------------------------------------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 32'd0;
        end else begin
            if (count < min_val)
                count <= min_val;
            else if (count > max_val)
                count <= max_val;
            else begin
                if (!next_direction) begin       // will be counting up
                    count <= at_max ? min_val : count + 1'b1;
                end else begin                   // will be counting down
                    count <= at_min ? max_val : count - 1'b1;
                end
            end
        end
    end

endmodule
