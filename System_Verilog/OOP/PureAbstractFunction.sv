virtual class BaseClass;
	int data;

	pure virtual function int getData();		// 就是完全沒有任何實作, 子類一定要對其實作, 要不然該子類也無法實例化 (其實就是 protype)
endclass

class ChildClass extends BaseClass;
	virtual function int getData();
		data = 32'hcafe_cafe;
		return data;
	endfunction
endclass

module tb;
	ChildClass child;
	initial begin
		child = new();
		$display ("data = 0x%0h", child.getData());
	end
endmodule

/*
	data = 0xcafecafes
*/