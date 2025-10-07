`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"
`include "my_monitor.sv"
`include "my_if.sv"
`include "my_env.sv"
`include "my_case0.sv"

module top_tb;

    reg clk;
    reg rst_n;

    /*
        在 top_tb 中做相應更改，多增加一組 my_if，並透過 config_db 將其設定為新的 env 中的 driver 和 monitor
    */
    
    my_if input_if0(clk, rst_n);
    my_if output_if0(clk, rst_n);
    my_if input_if1(clk, rst_n);
    my_if output_if1(clk, rst_n);

    dut my_dut(.clk(clk),
                .rst_n(rst_n),
                .rxd0(input_if0.data),
                .rx_dv0(input_if0.valid),
                .txd0(output_if0.data),
                .tx_en0(output_if0.valid),
                .rxd1(input_if1.data),
                .rx_dv1(input_if1.valid),
                .txd1(output_if1.data),
                .tx_en1(output_if1.valid));

    initial begin
        run_test("my_case0");   // 將 base test 改為 my_case0
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
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.i_agt.drv", "vif", input_if0);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.i_agt.mon", "vif", input_if0);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env0.o_agt.mon", "vif", output_if0);

        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.i_agt.drv", "vif", input_if1);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.i_agt.mon", "vif", input_if1);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.env1.o_agt.mon", "vif", output_if1);
    end

endmodule
