/*
  An Interface is a way to encapsulate signals into a block. 
  Also it becomes easier to connect with the DUT and other verification components.

  EX: APB bus protocol signals
      interface apb_if (input pclk);
        logic [31:0]    paddr;
        logic [31:0]    pwdata;
        logic [31:0]    prdata;
        logic           penable;
        logic           pwrite;
        logic           psel;
      endinterface

  Why are signals declared logic?
    - Drive signals of this type via assign statements (wire) and in a procedural block (reg)
    - 4-states

  Syntax:
  
    interface [name] ([port_list]);
      [list_of_signals]
    endinterface
  
    EX:
      interface myBus (input clk);
        logic [7:0]  data;
        logic      enable;

        // From TestBench perspective, 'data' is input and 'write' is output
        modport TB  (input data, clk, output enable);       => modport is used to define signal directions

        // From DUT perspective, 'data' is output and 'enable' is input
        modport DUT (output data, input enable, clk);
      endinterface

  Advantage:
    - Interfaces can contain tasks, functions, parameters, variables, functional coverage, and assertions. 
        Monitor and record the transactions via the interface within this block
    - Be easier to connect to design regardless of the number of ports 
        //Before interface
        dut dut0  (.data (data),
                  .enable (enable),
                  //  all other signals
                  );

        // With interface - higher level of abstraction possible
        dut dut0  (busIf.DUT);
*/

module dut (myBus busIf);
  always @ (posedge busIf.clk)
    if (busIf.enable)
      busIf.data <= busIf.data+1;
    else
      busIf.data <= 0;
endmodule


// Filename : tb_top.sv
module tb_top;
  bit clk;

  // Create a clock
  always #10 clk = ~clk;

  // Create an interface object
  myBus busIf (clk);

  // Instantiate the DUT; pass modport DUT of busIf
  dut dut0 (busIf.DUT);

  // Testbench code : let's wiggle enable
  initial begin
    busIf.enable  <= 0;
    #10 busIf.enable <= 1;
    #40 busIf.enable <= 0;
    #20 busIf.enable <= 1;
    #100 $finish;
  end
endmodule