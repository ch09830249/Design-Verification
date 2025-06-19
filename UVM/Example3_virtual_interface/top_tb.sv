`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"

module top_tb;

    reg clk;
    reg rst_n;

    my_if input_if(clk, rst_n);         // 定義了 interface 後，在 top_tb 中實例化 DUT 時，就可以直接使用，並將 interface 傳給其他組件來驅動或採樣 DUT
    my_if output_if(clk, rst_n);

    dut my_dut(.clk(clk),
               .rst_n(rst_n),
               .rxd(input_if.data),
               .rx_dv(input_if.valid),
               .txd(output_if.data),
               .tx_en(output_if.valid));

    initial begin
        /* 
            因為是用 run_test 去實例化 my_driver, 所以無法像操控 dut 一樣 
            (top_tb.my_dut.xxx 是可以的，但是 top_tb.my_driver.xxx 是不可以的)
            原因在於 UVM 透過 run_test 語句實例化了一個脫離了 top_tb 層次結構的實例，建立了一個新的層次結構
            所以需透過 config db 機制, set 寄信 get 收信
        */
        run_test("my_driver");
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

    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top", "vif", input_if);  // 使用雙冒號是因為這兩個函數都是靜態函數
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top", "vif2", output_if);
        /*
        set:
            virtual my_if:      uvm_config_db#（virtual my_if）則是一個參數化的類，其參數就是要寄信的類型，這裡是 virtual my_if
            null:
            "uvm_test_top":     表示的是路徑索引
            "vif":              此參數必須和 get 的第三個參數一致
            input_if:           表示要將哪個 interface 透過 config_db 傳遞給 my_driver
        */
    end

endmodule
