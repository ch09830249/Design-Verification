// 最簡單的 Up Counter 範例
module up_counter #(
    parameter WIDTH = 4  // 計數位元數
)(
    input  logic clk,
    input  logic rst,
    input  logic en,
    output logic [WIDTH-1:0] count
);

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            count <= 0;
        else if (en)
            count <= count + 1;
    end

endmodule


// 向下計數（Down Counter）
always_ff @(posedge clk or posedge rst) begin
    if (rst)
        count <= 0;
    else if (en)
        count <= count - 1;
end


// Up/Down Counter with Direction Control
input logic dir;  // 1 = up, 0 = down

always_ff @(posedge clk or posedge rst) begin
    if (rst)
        count <= 0;
    else if (en) begin
        if (dir)
            count <= count + 1;
        else
            count <= count - 1;
    end
end


// Mod-N Counter（N 為循環範圍）
parameter N = 10;

always_ff @(posedge clk or posedge rst) begin
    if (rst)
        count <= 0;
    else if (en) begin
        if (count == N-1)
            count <= 0;
        else
            count <= count + 1;
    end
end

// 簡單的除頻器（Divide-by-2）
logic clk_div2;

always_ff @(posedge clk or posedge rst) begin
    if (rst)
        clk_div2 <= 0;
    else
        clk_div2 <= ~clk_div2;
end
