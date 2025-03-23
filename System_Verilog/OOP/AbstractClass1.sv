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

/*
	data=0xfadefade
*/