/*
	If two classes need a handle to each other, the classic puzzle of whether chicken or egg came first pops up. 
	This is because the compiler processes the first class where it finds a reference to the second class being that 
	which hasn't been declared yet.
*/

class ABC;
	DEF 	def; 	// Error: DEF has not been declared yet
endclass

class DEF;
	ABC 	abc;
endclass

/*
	Typedef.sv:2: syntax error
	Typedef.sv:2: error: DEF doesn't name a type.
*/

// 所以要改成下面這樣

typedef class DEF;  // Inform compiler that DEF might be		Compiler 會去找
                    // used before actual class definition

class ABC;
	DEF 	def;      // Okay: Compiler knows that DEF
	                // declaration will come later
endclass

class DEF;
	ABC 	abc;
endclass

// 或是寫成這樣

typedef DEF; 		// Legal

class ABC;
	DEF def;
endclass

// 參數化 class 也可以用 typedef, 用法如下
typedef XYZ;

module top;
	XYZ #(8'h3f, real)              xyz0;   // positional parameter override
	XYZ #(.ADDR(8'h60), .T(real))   xyz1;  	// named parameter override
endmodule

class XYZ #(parameter ADDR = 8'h00, type T = int);
endclass