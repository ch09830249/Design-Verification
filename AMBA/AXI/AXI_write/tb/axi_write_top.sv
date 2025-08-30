`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module axi_write_top;

  logic clk = 0;
  logic rst_n = 0;

  always #5 clk = ~clk;

  axi_write_if axi_write_if(.ACLK(clk), .ARESETn(rst_n));

  axi_write_slave dut (
    .ACLK(clk),
    .ARESETn(rst_n),
    .AWADDR(axi_write_if.AWADDR),
    .AWVALID(axi_write_if.AWVALID),
    .AWREADY(axi_write_if.AWREADY),
    .WDATA(axi_write_if.WDATA),
    .WVALID(axi_write_if.WVALID),
    .WREADY(axi_write_if.WREADY),
    .BRESP(axi_write_if.BRESP),
    .BVALID(axi_write_if.BVALID),
    .BREADY(axi_write_if.BREADY)
  );

  initial begin
    rst_n = 0;
    #20                 // 20 ns 後 not rst 舉起來 => 開始運作
    rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual axi_write_if)::set(null, "*", "vif", axi_write_if);
    run_test("axi_write_test");
  end

  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
endmodule
