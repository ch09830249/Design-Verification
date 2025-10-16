`include "uvm_macros.svh"
import uvm_pkg::*;


`include "counter_if.sv"
`include "counter_seq_item.sv"
`include "counter_sequence.sv"
`include "counter_driver.sv"
`include "counter_monitor.sv"
`include "counter_scoreboard.sv"
`include "counter_agent.sv"
`include "counter_env.sv"
`include "counter_test.sv"

module tb_top;

  logic clk;
  always #5 clk = ~clk;

  counter_if cif(clk);

  counter dut (
    .clk(clk),
    .rst_n(cif.rst_n),
    .en(cif.en),
    .count(cif.count)
  );

  initial begin
    clk = 0;
    cif.rst_n = 0;
    cif.en = 0;
    #20;
    cif.rst_n = 1;
  end

  initial begin
    uvm_config_db#(virtual counter_if)::set(null, "*", "vif", cif);
    run_test("counter_test");
  end

endmodule