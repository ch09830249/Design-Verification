`timescale 1ns/1ps
`include "uvm_macros.svh"

import uvm_pkg::*;
`include "my_driver.sv"
`include "my_monitor.sv"
`include "my_if.sv"
`include "my_env.sv"

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

    initial begin
        run_test("my_env");
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

    /*
        在 my_env 的 build_phase 中，建立 i_agt 和 o_agt 的實例是在在 build_phase 中；在 agent 中，
        建立 driver 和 monitor 的實例也是在 build_phase 中。所以 build_phase 從樹根到樹葉的執行順序，
        可以建立一棵完整的UVM樹。
    */
    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.i_agt.drv", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.i_agt.mon", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.o_agt.mon", "vif", output_if);
    end

endmodule
