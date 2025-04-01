`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"

module top_tb;

    my_if input_if(clk, rst_n);
    my_if output_if(clk, rst_n);

    dut my_dut(.clk(clk),
                .rst_n(rst_n),
                .rxd(input_if.data),
                .rx_dv(input_if.valid),
                .txd(output_if.data),
                .tx_en(output_if.valid));

    initial begin
        run_test("my_env"); //run_test 的參數也從 my_driver 變成了 my_env：
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
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.drv", "vif", input_if);    // 樹狀結構改變, 所以在 top_tb 中使用 config_db 機制傳遞 virtualmy_if 時，要改變對應的路徑
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.drv", "vif2", output_if);
        /*
        uvm_test_top 是 UVM 自動建立的樹根的名字，而 drv 則是在 my_env 的 build_phase 中實例化 drv 時傳遞過去的名字。
        如果在實例化 drv 時傳遞的名字是 my_drv，那麼 set 函數的第二個參數中也應 my_drv
        */
    end

endmodule