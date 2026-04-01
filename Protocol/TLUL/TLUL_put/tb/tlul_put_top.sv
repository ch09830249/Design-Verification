`include "uvm_macros.svh"
import uvm_pkg::*;
  
module tlul_put_top;
  logic clk = 0;
  logic rst_n = 0;

  // Interface
  tlul_if tlul_if(clk, rst_n);

  // DUT instance
  tlul_put_slave dut (
    .clk      (clk),
    .rst_n    (rst_n),
    .a_valid  (tlul_if.a_valid),
    .a_ready  (tlul_if.a_ready),
    .a_opcode (tlul_if.a_opcode),
    .a_param  (tlul_if.a_param),
    .a_size   (tlul_if.a_size),
    .a_mask   (tlul_if.a_mask),
    .a_address(tlul_if.a_address),
    .a_data   (tlul_if.a_data),
    .a_source (tlul_if.a_source),

    .d_valid  (tlul_if.d_valid),
    .d_ready  (tlul_if.d_ready),
    .d_opcode (tlul_if.d_opcode),
    .d_param  (tlul_if.d_param),
    .d_size   (tlul_if.d_size),
    .d_data   (tlul_if.d_data),
    .d_source (tlul_if.d_source),
    .d_sink   (tlul_if.d_sink)
  );

  initial begin
    forever #5 clk = ~clk; // 100MHz clock
  end

  initial begin
    rst_n = 0;
    #20;
    rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual tlul_if)::set(null, "*", "vif", tlul_if);
    run_test("tlul_put_test");
  end

  initial begin
    $shm_open("waves.shm");
    $shm_probe("AS");
  end
endmodule
