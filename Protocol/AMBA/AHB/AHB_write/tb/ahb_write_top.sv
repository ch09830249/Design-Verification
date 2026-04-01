`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module ahb_write_top;

  logic clk = 0;
  logic rst_n = 0;

  always #5 clk = ~clk;

  ahb_if ahb_write_if(.HCLK(clk), .HRESETn(rst_n));

  ahb_write_slave dut (
    .HCLK    (ahb_write_if.HCLK),
    .HRESETn (ahb_write_if.HRESETn),
    .HADDR   (ahb_write_if.HADDR),
    .HTRANS  (ahb_write_if.HTRANS),
    .HWRITE  (ahb_write_if.HWRITE),
    .HSIZE   (ahb_write_if.HSIZE),
    .HWDATA  (ahb_write_if.HWDATA),
    .HRDATA  (ahb_write_if.HRDATA),
    .HREADY  (ahb_write_if.HREADY),
    .HRESP   (ahb_write_if.HRESP)
  );

  initial begin
    rst_n = 0;
    #20                 // 20 ns 後 not rst 舉起來 => 開始運作
    rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual ahb_if)::set(null, "*", "vif", ahb_write_if);
    run_test("ahb_write_test");
  end

  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
endmodule
