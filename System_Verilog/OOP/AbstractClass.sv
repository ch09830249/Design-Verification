/* 
	Abstract Class 禁止直接使用 
	SystemVerilog prohibits a class declared as virtual to be directly instantiated and is called an abstract class.
	強迫 developer 要去實作

	virtual class <class_name>
		// class definition
	endclass
*/
virtual class BaseClass;
	int data;

	function new();
		data = 32'hc0de_c0de;
	endfunction
endclass

module tb;
	BaseClass base;
	initial begin
		base = new();
		$display ("data=0x%0h", base.data);
	end
endmodule

/*
		base = new();
		   |
ncvlog: *E,CNIABC (testbench.sv,12|5): An abstract (virtual) class cannot be instantiated.
*/

virtual class BaseClass;
	int data;

	function new();
		data = 32'hc0de_c0de;
	endfunction
endclass

class ChildClass extends BaseClass;
	function new();
		data = 32'hfade_fade;
	endfunction
endclass

module tb;
	ChildClass child;
	initial begin
		child = new();
		$display ("data=0x%0h", child.data);
	end
endmodule