`timescale 1ns/1ps
`include "uvm_macros.svh"       // 把 uvm_macros.svh 檔案透過 include 語句包含進來。這是 UVM 中的一個文件，裡面包含了眾多的 macro 定義，只需要包含一次

import uvm_pkg::*;              // import 語句將整個 uvm_pkg 導入驗證平台中。只有導入了這個函式庫，編譯器在編譯 my_driver.sv 檔時才會認識其中的 uvm_driver 等類別名稱
`include "my_driver.sv"         // 把剛剛定義好的 driver 引入

module top_tb;

    reg clk;
    reg rst_n;
    reg [7:0] rxd;
    reg rx_dv;
    wire [7:0] txd;
    wire tx_en;

    dut my_dut(
        .clk(clk),
        .rst_n(rst_n),
        .rxd(rxd),
        .rx_dv(rx_dv),
        .txd(txd),
        .tx_en(tx_en)
    );

    initial begin
        run_test("my_driver");      // 改成這個
        /*
        一個 run_test 語句會建立一個 my_driver 的實例，並且會自動呼叫 my_driver 的 main_phase (要透過 uvm_component_utils 註冊過才行)
        1. 自動實例化已註冊的 class
        2. 自動呼叫該 class 的 _phase 函數
        */
    end

    initial begin
        clk = 0;
        forever begin
            #100 clk = ~clk;
        end
    end

    initial begin
        rst_n = 1'b0;
        #1000;
        rst_n = 1'b1;
    end

endmodule

/*
new is called
main_phased is called
*/