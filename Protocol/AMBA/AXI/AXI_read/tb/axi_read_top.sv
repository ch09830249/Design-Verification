`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module axi_read_top;

  logic clk = 0;
  logic rst_n = 0;

  always #5 clk = ~clk;

  axi_read_if axi_vif(.ACLK(clk), .ARESETn(rst_n));

  axi_read_slave u_read (
    .ACLK(clk),
    .ARESETn(rst_n),
    .ARADDR(axi_vif.ARADDR),
    .ARVALID(axi_vif.ARVALID),
    .ARREADY(axi_vif.ARREADY),
    .RDATA(axi_vif.RDATA),
    .RRESP(axi_vif.RRESP),
    .RVALID(axi_vif.RVALID),
    .RREADY(axi_vif.RREADY)
  );

  initial begin
    rst_n = 0;
    #20                 // 20 ns 後 not rst 舉起來 => 開始運作
    rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual axi_read_if)::set(null, "*", "vif", axi_vif);
    run_test("axi_read_test");
  end

  initial begin
        $shm_open("waves.shm");
        $shm_probe("AS");
  end

endmodule
