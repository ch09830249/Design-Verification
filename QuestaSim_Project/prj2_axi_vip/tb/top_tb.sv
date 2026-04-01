// 整體 top-level testbench
`timescale 1ns/1ps
`include "../rtl/axi_if.sv"

module top_tb;

    import uvm_pkg::*;
    `include "uvm_macros.svh"
    import axi_pkg::*;

    bit ACLK = 0;
    bit ARESETn = 0;

    always #5 ACLK = ~ACLK;

    axi_if axi_if_inst(.ACLK(ACLK), .ARESETn(ARESETn));

    // DUT
    axi_slave_dut dut (
        .ACLK(ACLK),
        .ARESETn(ARESETn),
        .AWID(axi_if_inst.AWID),
        .AWADDR(axi_if_inst.AWADDR),
        .AWLEN(axi_if_inst.AWLEN),
        .AWVALID(axi_if_inst.AWVALID),
        .AWREADY(axi_if_inst.AWREADY),

        .WDATA(axi_if_inst.WDATA),
        .WVALID(axi_if_inst.WVALID),
        .WREADY(axi_if_inst.WREADY),
        .WLAST(axi_if_inst.WLAST),

        .BID(axi_if_inst.BID),
        .BRESP(axi_if_inst.BRESP),
        .BVALID(axi_if_inst.BVALID),
        .BREADY(axi_if_inst.BREADY),

        .ARID(axi_if_inst.ARID),
        .ARADDR(axi_if_inst.ARADDR),
        .ARLEN(axi_if_inst.ARLEN),
        .ARVALID(axi_if_inst.ARVALID),
        .ARREADY(axi_if_inst.ARREADY),

        .RID(axi_if_inst.RID),
        .RDATA(axi_if_inst.RDATA),
        .RRESP(axi_if_inst.RRESP),
        .RVALID(axi_if_inst.RVALID),
        .RLAST(axi_if_inst.RLAST),
        .RREADY(axi_if_inst.RREADY)
    );

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
