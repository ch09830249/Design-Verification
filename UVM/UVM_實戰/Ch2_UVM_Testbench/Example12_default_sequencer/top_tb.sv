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

    initial begin
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.i_agt.drv", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.i_agt.mon", "vif", input_if);
        uvm_config_db#(virtual my_if)::set(null, "uvm_test_top.o_agt.mon", "vif", output_if);
    end

    /* 
        在 top_tb 中設定 virtual interface 時，由於 top_tb 不是一個類，無法使用 this 指針，所以設定 set 的第一個參數為 null，
        第二個參數使用 uvm_test_top.XXX
    */
    
    // 除了在 my_env 的 build_phase 中設定 default_sequence 外，還可以在其他地方設置，例如 top_tb (這裡的第一和第二參數就需要改變一下)
    // initial begin
    //     uvm_config_db#(uvm_object_wrapper)::set(null,
    //                                             "uvm_test_top.i_agt.sqr.main_phase",
    //                                             "default_sequence",
    //                                             my_sequence::type_id::get());
    // end

endmodule
