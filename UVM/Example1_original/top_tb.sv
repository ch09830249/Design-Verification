`timescale 1ns/1ps
`include "uvm_macros.svh"       // 把 uvm_macros.svh 檔案透過 include 語句包含進來。這是 UVM 中的一個文件，裡面包含了眾多的 macro 定義，只需要包含一次

import uvm_pkg::*;              // import 語句將整個 uvm_pkg 導入驗證平台中。只有導入了這個函式庫，編譯器在編譯 my_driver.sv 檔時才會認識其中的 uvm_driver 等類別名稱
`include "my_driver.sv"         // 把剛剛定義好的 driver 引入

module top_tb;

    // 以下皆是要串連 dut 的變數
    reg clk;
    reg rst_n;
    reg [7:0] rxd;
    reg rx_dv;
    wire [7:0] txd;
    wire tx_en;

    // 將 top_tb 和 dut 的 input 連接
    dut my_dut(
        .clk(clk),
        .rst_n(rst_n),
        .rxd(rxd),
        .rx_dv(rx_dv),
        .txd(txd),
        .tx_en(tx_en)
    );

    initial begin
        my_driver drv;          // 創建 my_driver 的 handle 並將其實例化   PS: 前文介紹 uvm_info 巨集的列印資訊時出現的代表路徑索引的 drv 就是在這裡傳入的參數 drv
        drv = new("drv", null); // 前面介紹 uvm_info 巨集的列印資訊時出現的代表路徑索引的 drv 就是在這裡傳入的參數 drv。
        drv.main_phase(null);   // 呼叫 my_driver 的 main_phase。在 main_phase 的聲明中，有一個 uvm_phase 類型的參數phase，在真正的驗證平台，這個參數是不需要使用者理會的。本節的驗證平台還不算完整的UVM驗證平台，所以暫且傳入null。
        $finish();              // 呼叫 finish 函數結束整個仿真，這是一個 Verilog 提供的函數
    end

    initial begin
        clk = 0;
        forever begin
            #100 clk = ~clk;
        end
    end

    initial begin
        rst_n = 1'b0;           // 先清空 rxd 和 rx_dv, 等 1000 ns 後, 才正常傳送資料
        #1000;
        rst_n = 1'b1;
    end

endmodule

/*
    可以看到「data is drived」被輸出了 256 次。
*/