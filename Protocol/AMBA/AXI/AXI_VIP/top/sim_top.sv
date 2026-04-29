`timescale 1ps/1ps

`include "axi_define.svh"
`include "axi_protocol_sva.sv"
`include "axi_interface.sv"
`include "bind_axi_protocol_sva.sv"

import uvm_pkg::*;

`include "axi_package.svh"
import axi_package::*;

module sim_top;

    logic           clk, rst_n;
    axi_interface   vif();

    assign vif.ACLK    = clk;
    assign vif.ARESETn = rst_n;

    // axi_slave_bfm slv (
    //     .ACLK   (clk),
    //     .ARESETn(rst_n),
    //     .vif    (vif)
    // );

    always #5 clk = ~clk;

    initial begin
        clk   = 0;
        rst_n = 0;
        uvm_config_db #(virtual axi_interface)::set(null, "*", "vif", vif);
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
