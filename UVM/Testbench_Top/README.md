# UVM Testbench Top
![image](https://github.com/user-attachments/assets/adee9b11-c376-4b1c-94a3-b90b261e8178)  
* All verification **components**, **interfaces** and **DUT** are instantiated in a top level module called testbench. It is a static container to hold everything required to be simulated and becomes the root node in the hierarchy. This is usually named **tb** or **tb_top** although it can assume any other name.
# Testbench Top Example
```
module tb_top;
   import uvm_pkg::*;    // 需要 import uvm_pkg 以使用 UVM constructs

   // Complex testbenches will have multiple clocks and hence multiple clock
   // generator modules that will be instantiated elsewhere
   // For simple designs, it can be put into testbench top
   bit clk;    // 產生 module 所需的 clk
   always #10 clk <= ~clk; 


   // Instantiate the Interface and pass it to Design
   dut_if         dut_if1  (clk);               // 實例化 interface 和 module, 先將 clock 傳入 interface
   dut_wrapper    dut_wr0  (._if (dut_if1));    // 將 interface 物件傳給 module


   // At start of simulation, set the interface handle as a config object in UVM
   // database. This IF handle can be retrieved in the test using the get() method
   // run_test () accepts the test name as argument. In this case, base_test will
   // be run for simulation
   initial begin
      // 將該 interface handle 設置於 configuration table, 要使用該 handle 都可以透過 get() 方法去取用
      uvm_config_db #(virtual dut_if)::set (null, "uvm_test_top", "dut_if", dut_if1);
      // run simulation 名為 base_test
      run_test ("base_test");
   end

   // Multiple EDA tools have different system task calls to specify and dump waveform
   // in a given format or path. Some do not need anything to be placed in the testbench
   // top module. Lets just dump a very generic waveform dump file in *.vcd format
   initial begin
      // Dump wave
      $dumpvars;
      // 存成 .vcd 檔
      $dumpfile("dump.vcd");
   end

endmodule
```
