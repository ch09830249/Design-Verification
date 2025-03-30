# What is the difference between logic and bit in SystemVerilog?
A bit is a single binary digit that can have a value of 0 or 1,  
while logic is a data type used for representing a single wire or net that can have multiple states  
such as 0, 1, Z (high-impedance), X (unknown), or L (weakly driven low) and H (weakly driven high).

# How to check if any bit of the expression is X or Z?
```
// To check if all bits of variable "xyz" are Z
if (xyz === 'Z) begin
	$display("All bits in xyz are Z");
end

// To check if any bit in "xyz" is Z
if ($countbits(xyz, 'Z)) begin
	$display("Some bit in xyz is Z");
end

// To check if signal is X
if ($isunknown(xyz)) begin
	$display("xyz is unknown or has value X");
end
```

# Figure out a solution to the following puzzle.
Assume two base classes A and B, and two derived classes C and D where this relation between classes is unknown to end user. How do you find base class for each derived class?
```
class A;
class B;

// Assume this relation is hidden from end user
class C extends B;
class D extends A;

module tb;
	initial begin
		A 	m_a = new();
		B 	m_b = new();
		C 	m_c = new();
		D 	m_d = new();
		// function int $cast (targ_var, source_exp);
		// Successful cast implies that the second arg is a child of first arg		透過子類物件可以轉成父類物件, 但反之則舞法的特性, 去檢查
		if ($cast(m_a, m_c))
			$display("C is a child of A");
		if ($cast(m_a, m_d))
			$display("D is a child of A");
		if ($cast(m_b, m_c))
			$display("C is a child of B");
		if ($cast(m_b, m_d)
			$display("D is a child of B");
	end
endmodule
```

# Write SV code to wait for a random delay in range 100 to 500 ns.
Delays are indicated by the # construct and a random delay can be written as follows.
```
`timescale 1ns/1ps

module tb;
	initial begin
		int delay;

		std::randomize(delay) with { delay inside {[100:500]}; };	// in-line constraint
		#(delay) $display("Statement printed after %0d delay", delay);

		// This is also good enough, although there's no variable to print actual randomized delay
		#($urandom_range(100, 500)) $display("Some delay between 100 to 500");
	end
endmodule
```

# What is the difference between a parameter and typedef?
**parameter is used to define compile-time constants used within modules**, which are values that can be evaluated and assigned before the simulation starts.  
It can be used to specify parameters such as width, depth, or delay of modules.
```
module my_module #(parameter WIDTH=8) (
    input [WIDTH-1:0] data_in,
    output [WIDTH-1:0] data_out
);
    // module logic here
endmodule
```
自定義一個 data types
**typedef is used to define custom data types that can be reused throughout the design**. It can be used to define complex data types such as structures, arrays, and enumerated types.  
It is used to make the code more readable and easier to understand by encapsulating complex data types within a single type name.
```
typedef struct {
    logic [7:0] addr;
    logic [31:0] data;
} request_t;

request_t my_req;

my_req.addr = 8'h22;
my_req.data = 32'h12345678;
```

# What is constraint solve-before?
solve - before is a constraint solver directive that allows constraints to be solved in a specific order. This directive specifies that a particular constraint should be solved before another constraint. It is useful in cases where certain constraints must be solved before others to avoid conflicts or to ensure that specific constraints are satisfied.

# What is an alias?
**alias is a keyword used to declare an alternate name for a variable or net**.  
It allows access to the same object through multiple names. The new name created using the alias keyword refers to the same variable or memory location as the original variable.
```
wire [7:0]      _byte;
wire 		_bit;

alias bits_9 = { _byte, _bit };
```

# Write code to extract 5 elements at a time from a queue.
```
module tb;
	bit [7:0] 	q [$];
	bit [7:0] 	tmp [$];

	initial begin
		repeat (9) q.push_back($random);	// 推 9 個數進 queue

		for (byte i = 0; i < q.size(); i += 5)
			tmp = q[i +: 5];
	end

endmodule
```

# What is the difference between the clocking block and modport?
A clocking block is used to model clock and reset signals and their associated timing control signals. It provides a way of defining a set of timing signals as well as their phases and signal transitions.

A modport is used to group a set of port declarations into a named entity. It allows designers to specify multiple port configurations and to limit access to specific module interfaces.

# What is the difference between $random and $urandom?
$random returns signed integer values, whereas $urandom returns an unsigned integer value.
```
int 	 	data1;
bit [31:0] 	data2;

data1 = $random; 	// signed integer
data2 = $urandom;  	// unsigned integer
```

