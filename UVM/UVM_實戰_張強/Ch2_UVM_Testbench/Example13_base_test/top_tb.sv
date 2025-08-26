`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"
`include "my_monitor.sv"
`include "my_if.sv"
`include "my_env.sv"
`include "base_test.sv"

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

    // top_tb 中 run_test 的參數從 my_env 變成了 base_test
    initial begin
        run_test("base_test");
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

    // 並且 config_db 設定 virtual interface 的路徑參數要做如下改變：
    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.drv", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.i_agt.mon", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env.o_agt.mon", "vif", output_if);
    end

endmodule
