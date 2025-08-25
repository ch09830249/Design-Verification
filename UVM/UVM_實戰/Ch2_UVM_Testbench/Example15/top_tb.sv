`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"
`include "my_monitor.sv"
`include "my_if.sv"
`include "my_env.sv"
`include "base_test.sv"
`include "my_case0.sv"
`include "my_case1.sv"

module top_tb;

    reg clk;
    reg rst_n;
    
    my_if input_if(clk, rst_n);
    my_if output_if(clk, rst_n);

    dut my_dut(.clk(clk),
                .rst_n(rst_n),
                .rxd(input_if.data),
                .rx_dv(input_if.valid),
                .txd(output_if.data),
                .tx_en(output_if.valid));

    /*
        要啟動 my_case0 或 my_case1，需要在 top_tb 中更改 run_test 的參數
        initial begin
            run_test("my_case0");
        end

        initial begin
            run_test("my_case1");
        end
    */

    /*
        當 my_case0 運行的時候需要修改程式碼，重新編譯後才能運行；
        當 my_case1 運行時也需如此，這相當不方便。事實上，UVM 提供對不加參數的 run_test 的支持
        在這種情況下，UVM 會利用 UVM_TEST_NAME 從命令列中尋找測試案例的名字，創建它的實例並運行
        EX:
            <sim command>
            … +UVM_TEST_NAME=my_case0
            or
            … +UVM_TEST_NAME=my_case1
    */

    initial begin
        // run_test();
        // run_test("my_case0");
        run_test("my_case1");
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
        $shm_open("waves.shm");
        $shm_probe("AS");
    end

    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.drv", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.mon", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.o_agt.mon", "vif", output_if);
    end

endmodule
