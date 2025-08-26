module dut(clk, rst_n, rxd, rx_dv, txd, tx_en);
    input clk;
    input rst_n;
    input[7:0] rxd;
    input rx_dv;
    output [7:0] txd;
    output tx_en;

    reg[7:0] txd;
    reg tx_en;

    always @(posedge clk) begin     // 在 clk 上沿時 module 做事
        if(!rst_n) begin            // 若 rst_n 為 0, 將 txd 和 tx_en 清掉
            txd <= 8'b0;
            tx_en <= 1'b0;
        end
        else begin
            txd <= rxd;             // 否則將 rxd 接收到的數據給 txd
            tx_en <= rx_dv;         // 並且根據 rx_dv 表示該 txd 是否有效的資料
        end
    end
endmodule

/*
    透過 rxd 接收數據，再透過 txd 發送出去。其中 rx_dv 是接收的資料有效指示，tx_en 是發送的資料有效指示
    資料都是一個 Byte 一個 Byte 傳遞
*/
