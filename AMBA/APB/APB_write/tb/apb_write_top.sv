`timescale 1ns/1ps
import uvm_pkg::*;
`include "uvm_macros.svh"

module apb_write_top;

  logic PCLK = 0;
  logic PRESETn = 0;

  apb_write_if apb_if_inst(.PCLK(PCLK), .PRESETn(PRESETn));

  apb_write_slave dut (
    .PCLK   (PCLK),
    .PRESETn(PRESETn),
    .PSEL   (apb_if_inst.PSEL),
    .PENABLE(apb_if_inst.PENABLE),
    .PWRITE (apb_if_inst.PWRITE),
    .PADDR  (apb_if_inst.PADDR),
    .PWDATA (apb_if_inst.PWDATA),
    .PREADY (apb_if_inst.PREADY)
  );

  // Clock generator
  always #5 PCLK = ~PCLK;

  // Reset generator
  initial begin
    PRESETn = 0;
    #20;
    PRESETn = 1;
  end

  initial begin
    uvm_config_db#(virtual apb_write_if)::set(null, "*", "vif", apb_if_inst);
    run_test("apb_write_test");
  end

  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
endmodule
