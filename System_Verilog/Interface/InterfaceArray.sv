/*
  // interface myInterface;

  interface myInterface ();
    reg 		gnt;
    reg 		ack;
    reg [7:0]	irq;

    ...
  endinterface

  module tb;
    // Single interface handle
    myInterface 	if0 ();

    // An array of interfaces (4 個 interface)
    myInterface 	wb_if [3:0] ();

    // Rest of the testbench
  endmodule
*/

module myDesign ( myInterface dut_if,
                  input logic clk);

	always @(posedge clk)
		if (dut_if.ack)
			dut_if.gnt <= 1;

endmodule

module tb;
	reg clk;

	// Single interface handle connection
	myInterface  if0;

  // An array of interfaces (4 個 interface)
  myInterface 	wb_if [3:0] ();
  
	myDesign 	 top (if0, clk);

	// Or connect by name
	// myDesign  top (.dut_if(if0), .clk(clk));

	// Multiple design instances connected to the appropriate
	// interface handle
	myDesign 	md0 (wb_if[0], clk);
	myDesign 	md1 (wb_if[1], clk);
	myDesign 	md2 (wb_if[2], clk);
	myDesign 	md3 (wb_if[3], clk);

endmodule

/*
*/