/*

*/

module tb_top;
   import uvm_pkg::*;

   // Complex testbenches will have multiple clocks and hence multiple clock
   // generator modules that will be instantiated elsewhere
   // For simple designs, it can be put into testbench top
   bit clk;
   always #10 clk <= ~clk;


   // Instantiate the Interface and pass it to Design
   dut_if         dut_if1  (clk);
   dut_wrapper    dut_wr0  (._if (dut_if1));


   // At start of simulation, set the interface handle as a config object in UVM
   // database. This IF handle can be retrieved in the test using the get() method
   // run_test () accepts the test name as argument. In this case, base_test will
   // be run for simulation
   initial begin
      uvm_config_db #(virtual dut_if)::set (null, "uvm_test_top", "dut_if", dut_if1);
      run_test ("base_test");
   end

   // Multiple EDA tools have different system task calls to specify and dump waveform
   // in a given format or path. Some do not need anything to be placed in the testbench
   // top module. Lets just dump a very generic waveform dump file in *.vcd format
   initial begin
   		$dumpvars;
   		$dumpfile("dump.vcd");
   end

endmodule