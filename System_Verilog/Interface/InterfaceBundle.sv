/*
  Using a name bundle
*/

module myDesign  (  myInterface  if0,   // 這裡直接用定義好的 myInterface 名稱
                    input logic  clk);
	always @ (posedge clk)
		if (if0.ack)
			if0.gnt <= 1;

	...
endmodule

module yourDesign (  myInterface 	if0,
					 input logic 	clk);
	...

endmodule

module tb;
	logic clk = 0;

	myInterface 	_if;  // 先例化定義好的 myInterface

	myDesign 	md0 	(_if, clk); // 再傳入 module
	yourDesign	yd0 	(_if, clk);

endmodule

/*
  Using a genric bundle
*/

module myDesign  ( interface  a,
                   input logic  clk);

	always @ (posedge clk)
		if (if0.ack)
			if0.gnt <= 1;

	...
endmodule

module yourDesign (  interface 		b,
					 input logic 	clk);
	...

endmodule

module tb;
	logic clk = 0;

	myInterface  _if;

	myDesign 	md0 ( .*, .a(_if));   // use partial implicit port connections  => 怪怪的 Weird
	yourDesign	yd0 ( .*, .b(_if));

endmodule