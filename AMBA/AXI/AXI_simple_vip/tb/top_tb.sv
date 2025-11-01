// 整體 top-level testbench
`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module top_tb;

    bit clk = 0;
    bit rst_n  = 0;

    always #5 clk = ~clk;

    axi_if axi_if_inst(.ACLK(clk), .ARESETn(rst_n));

    // DUT
    axi_slave_dut dut (
        .ACLK(clk),
        .ARESETn(rst_n),
        .AWID(axi_if_inst.AWID),
        .AWADDR(axi_if_inst.AWADDR),
        .AWLEN(axi_if_inst.AWLEN),
        .AWSIZE(axi_if_inst.AWSIZE),
        .AWBURST(axi_if_inst.AWBURST),
        .AWLOCK(axi_if_inst.AWLOCK),
        .AWCACHE(axi_if_inst.AWCACHE),
        .AWPROT(axi_if_inst.AWPROT),
        .AWQOS(axi_if_inst.AWQOS),
        .AWVALID(axi_if_inst.AWVALID),
        .AWREADY(axi_if_inst.AWREADY),

        .WDATA(axi_if_inst.WDATA),
        .WSTRB(axi_if_inst.WSTRB),
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
        .ARSIZE(axi_if_inst.ARSIZE),
        .ARBURST(axi_if_inst.ARBURST),
        .ARLOCK(axi_if_inst.ARLOCK),
        .ARCACHE(axi_if_inst.ARCACHE),
        .ARPROT(axi_if_inst.ARPROT),
        .ARQOS(axi_if_inst.ARQOS),
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
        rst_n = 0;
        // repeat (5) @(posedge clk);
        #48
        rst_n = 1;
    end

    initial begin
        uvm_config_db#(virtual axi_if)::set(null, "*", "vif", axi_if_inst);
        run_test("axi_test");
    end

    initial begin
        $shm_open("waves.shm");
        $shm_probe("AS");
    end

endmodule
