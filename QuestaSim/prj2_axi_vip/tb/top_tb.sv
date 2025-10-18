// 整體 top-level testbench
`timescale 1ns/1ps

module top_tb;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import axi_pkg::*;

    bit ACLK = 0;
    bit ARESETn = 0;

    always #5 ACLK = ~ACLK;

    axi_if axi_if_inst(.ACLK(ACLK), .ARESETn(ARESETn));

    initial begin
        ARESETn = 0;
        repeat (5) @(posedge ACLK);
        ARESETn = 1;
    end

    initial begin
        uvm_config_db#(virtual axi_if)::set(null, "*", "vif", axi_if_inst);
        run_test("axi_test");
    end

endmodule
