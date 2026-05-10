// =============================================================================
// File    : counter.v
// Desc    : 32-bit up/down counter with min/max boundary and reverse control
//           - Counts up:   min, min+1, ..., max, min, min+1, ...
//           - Counts down: max, max-1, ..., min, max, max-1, ...
//           - reverse==1 (single cycle pulse) toggles direction
//           - Hitting boundary also auto-toggles direction
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

    // -------------------------------------------------------------------------
    // Direction control
    // -------------------------------------------------------------------------
    wire at_max = (count == max_val);
    wire at_min = (count == min_val);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            direction <= 1'b0;           // start counting up
        end else begin
            // reverse pulse overrides; boundary bounce happens simultaneously
            if (reverse) begin
                direction <= ~direction;
            end else begin
                if (!direction && at_max)
                    direction <= 1'b1;   // reached top -> go down
                else if (direction && at_min)
                    direction <= 1'b0;   // reached bottom -> go up
            end
        end
    end

    // -------------------------------------------------------------------------
    // Counter
    // -------------------------------------------------------------------------
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 32'd0;
        end else begin
            // Clamp count to [min_val, max_val] on reset de-assertion
            if (count < min_val)
                count <= min_val;
            else if (count > max_val)
                count <= max_val;
            else begin
                if (!direction) begin                // counting up
                    count <= at_max ? min_val : count + 1'b1;
                end else begin                       // counting down
                    count <= at_min ? max_val : count - 1'b1;
                end
            end
        end
    end

endmodule
