`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"

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
        // original code
        // my_driver drv;
        // drv = new("drv", null);
        // drv.main_phase(null);
        // $finish();
        run_test("my_driver");      // 改成這個  PS: UVM 根據 "my_driver" 這個字串創建了其所代表類別的一個實例
        /*
        一個 run_test 語句會建立一個 my_driver 的實例，並且會自動呼叫 my_driver 的 main_phase (要透過 uvm_component_utils 註冊過才行)
        1. 自動實例化已註冊的 class
        2. 自動呼叫該 class 的 _phase 函數
        */
        /*
        在 UVM 驗證平台中，只要一個類別使用 uvm_component_utils 註冊且此類被實例化，那麼這個類別的 main_phase 就會自動被呼叫。
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

    initial begin
        $shm_open("waves.shm");        // 指定 SHM 波形檔名
        $shm_probe("AS");              // 把 top_tb 裡所有訊號都 dump 出來
    end

endmodule

/*
    new is called
    main_phased is called       這裡因為沒有 objection 所以沒有 data is driven (沒有在 my_driver 中的 main_phase 去 raise objection)
*/
