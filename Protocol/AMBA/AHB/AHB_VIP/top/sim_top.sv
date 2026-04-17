`timescale 1ps/1ps

`include "ahb_define.svh"
`include "ahb_protocol_sva.sv"
`include "ahb_interface.sv"
`include "bind_ahb_protocol_sva.sv"

import uvm_pkg::*;

`include "ahb_package.svh"
import ahb_package::*;

module sim_top;

    logic           clk, rst_n;
    ahb_interface   vif();

    assign vif.HCLK    = clk;
    assign vif.HRESETn = rst_n;

    // ahb_slave_bfm slv (
    //     .PCLK   (clk),
    //     .PRESETn(rst_n),
    //     .vif    (vif)
    // );


    always #5 clk = ~clk;

    initial begin
        clk   = 0;
        rst_n = 0;
        uvm_config_db #(virtual ahb_interface) :: set (null, "*", "vif", vif);
        #10;
        rst_n = 1;
    end

    initial begin
        $shm_open("wave.shm");
        $shm_probe("AS");
    end

    initial begin
        run_test();
    end

endmodule
