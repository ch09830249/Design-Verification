`timescale 1ps/1ps

`include "apb_define.svh"
`include "apb_protocol_sva.sv"
`include "apb_interface.sv"
`include "bind_apb_protocol_sva.sv"

import uvm_pkg::*;

`include "apb_package.svh"
import apb_package::*;

// `include "apb_slave_bfm.sv"

module sim_top;

    logic           clk, rst_n;
    apb_interface   vif();

    assign vif.PCLK    = clk;
    assign vif.PRESETn = rst_n;

    // apb_slave_bfm slv (
    //     .PCLK   (clk),
    //     .PRESETn(rst_n),
    //     .vif    (vif)
    // );

    always #5 clk = ~clk;

    initial begin
        clk   = 0;
        rst_n = 0;
        uvm_config_db #(virtual apb_interface) :: set (null, "*", "vif", vif);
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
