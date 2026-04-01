`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module ahb_read_top;

  logic clk = 0;
  logic rst_n = 0;

  always #5 clk = ~clk;

  ahb_if ahb_read_if(clk, rst_n);

  ahb_read_slave slave (
    .HCLK(clk),
    .HRESETn(rst_n),
    .HADDR(ahb_read_if.HADDR),
    .HTRANS(ahb_read_if.HTRANS),
    .HWRITE(ahb_read_if.HWRITE),
    .HSIZE(ahb_read_if.HSIZE),
    .HWDATA(ahb_read_if.HWDATA),
    .HRDATA(ahb_read_if.HRDATA),
    .HREADY(ahb_read_if.HREADY),
    .HRESP(ahb_read_if.HRESP)
  );

  initial begin
    rst_n = 0;
    #20                 // 20 ns 後 not rst 舉起來 => 開始運作
    rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual ahb_if)::set(null, "*", "vif", ahb_read_if);
    run_test("ahb_read_test");
  end

  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
endmodule
