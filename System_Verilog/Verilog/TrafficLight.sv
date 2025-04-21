// Verilog 實作（同步 FSM）
// 這是一個同步設計，假設使用 1Hz 時脈來代表「1 秒」（實際可以用除頻器產生）
module traffic_light (
    input  logic clk,
    input  logic rst,
    output logic [1:0] ns_light,  // 00=紅, 01=綠, 10=黃
    output logic [1:0] ew_light
);

    // 狀態編碼
    typedef enum logic [1:0] {
        NS_GREEN,
        NS_YELLOW,
        EW_GREEN,
        EW_YELLOW
    } state_t;

    state_t state, next_state;

    logic [3:0] timer;  // 用來計數秒數

    // 狀態轉移條件
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state <= NS_GREEN;
            timer <= 0;
        end else begin
            if (timer == 0)
                state <= next_state;
            else
                timer <= timer - 1;
        end
    end

    // 決定下一狀態 & timer 設定
    always_comb begin
        next_state = state; // 預設維持原狀態
        case (state)
            NS_GREEN: begin
                if (timer == 0) begin
                    next_state = NS_YELLOW;
                    timer = 2;
                end
            end
            NS_YELLOW: begin
                if (timer == 0) begin
                    next_state = EW_GREEN;
                    timer = 5;
                end
            end
            EW_GREEN: begin
                if (timer == 0) begin
                    next_state = EW_YELLOW;
                    timer = 2;
                end
            end
            EW_YELLOW: begin
                if (timer == 0) begin
                    next_state = NS_GREEN;
                    timer = 5;
                end
            end
        endcase
    end

    // 控制燈號輸出
    always_comb begin
        case (state)
            NS_GREEN:  begin ns_light = 2'b01; ew_light = 2'b00; end
            NS_YELLOW: begin ns_light = 2'b10; ew_light = 2'b00; end
            EW_GREEN:  begin ns_light = 2'b00; ew_light = 2'b01; end
            EW_YELLOW: begin ns_light = 2'b00; ew_light = 2'b10; end
            default:   begin ns_light = 2'b00; ew_light = 2'b00; end
        endcase
    end

endmodule

/*
    燈號定義（方便用 LED 控制）
    編碼	顏色
    00	    紅
    01	    綠
    10	    黃
*/