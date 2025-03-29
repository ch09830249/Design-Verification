# What is `timescale?
The `timescale directive is used to set the time units and precision for a design. It specifies the time scale used in the simulation and the unit of time for delays and times associated with signal assignments and other operations.
```
`timescale <time_unit>/<time_precision>

// Example
`timescale 1ns/1ps
`timescale 10us/100ns
`timescale 10ns/1ns
```

# What are the basic testbench components?
A basic testbench consists of the following components:

Stimulus generation: Stimulus generation involves creating test vectors or other input signals that will be applied to the inputs of the design under test (DUT).
Interface: The interface provides the communication between the testbench and the DUT. It includes input and output ports, which are connected to the corresponding signals in the DUT.
Driver: The driver is responsible for converting stimulus into pin toggles appropriate to the bus protocol used by the DUT.
Monitor: The monitor observes the output signals of the DUT and produces a stream of data that the testbench can analyze.
Scoreboard: The scoreboard compares the output of the DUT with the expected output, and generates an error message or other notification if there is a mismatch.
Coverage analysis: Coverage analysis measures how much of the design has been exercised during simulation, and helps identify parts of the design that may not have been tested thoroughly.

# What is circular dependency?
Circular dependency is a situation in which two or more components or entities of a system depend on each other in a circular way, creating a cycle. It can occur between modules, functions, or libraries that depend on each other in a way that creates a loop. This can lead to issues when trying to compile or link the code, as the dependencies cannot be resolved. This can be solved with forward declaration by typedef.
```
// Declaration beforehand that a class called B will be
// defined somewhere later in the same file
typedef class B;

class A;
	B 	b;

	...
endclass

// For some reason an object of A is required in B causing
// a dependency loop
class B;
	A 	a;

endclass
```

# What are the advantages of a SystemVerilog program block?
Statements inside a program block are executed in the reactive region which is executed the last in a Verilog simulator event scheduler and hence can react on final state of design signals. It acts as an entry point for test stimulus to be executed by the testbench. It can contain functions, tasks and other supported constructs that enable user to create meaningful test stimulus.

# What is scope randomization?
Scope randomization allows to define different randomization constraints for different parts or scopes of the design hierarchy.
```
module tb;
	byte data;

	initial begin
		randomize(data) with { data > 0 };
		$display("data = 0x%0h", data);
	end
endmodule
```
Note that std:: is required if you need to call from within a class method to distinguish it from the class's built-in randomize method.

# What is the input skew and output skew in the clocking block?
A clocking block is a feature in SystemVerilog used to manage clock signals in a design. Input skew refers to when a signal defined as input to the clocking block should be sampled relative to the given edge of the clock. Output skew refers to when a signal declared as an output to the clocking block should be driven relative to the given edge of the clock.
```
clocking cb @(posedge clk);
	default input #1step output #1ns;
	input 	hready;
	output 	haddr;
endclocking
```

# Explain the different stages a simulator goes through to run a simulation.
Simulators typically comprises three simulation phases. These phases are:

Compilation Phase: This phase involves compiling the design and testbench files and checks the syntax, semantics, and hierarchy of the design, including all modules and interfaces.
Elaboration Phase: During this phase, the SystemVerilog compiler parses the design files and creates an internal representation of the design in memory. It reads the testbench code, generates object files, and links them together to create an executable file. It also includes the loading of any libraries, linking with external modules, and optimizing the executable file. Any issues found during elaboration must be resolved before simulation can proceed.
Simulation Phase: This is the actual running of the simulation. The simulation takes the compiled executable file and simulates the hardware design under test. The simulation initializes the testbench and DUT, applies stimulus to the DUT, and checks the expected output. The SystemVerilog simulation engine checks for timing, race conditions, and other errors and generates a log file during the simulation.

# What is casting?
Casting is a fundamental concept in programming and refers to the process of converting one data type into another data type. In SystemVerilog, casting is mainly used for type conversion between numeric and non-numeric data types.
```
real pi = 3.14;
int  a = int'(pi) * 10; 	// Cast real into an integer number

$cast(aa, a); 				// Cast object 'a' into 'aa'
```

# How to generate array without randomization?
This solution does not generate fully random numbers, however it does give unique values.
```
module tb;
	byte 	data_q [10];

	initial begin
		// Store numbers 0 through 10
		foreach (data_q [i])
			data_q[i] = i;

		// Shuffle the array
		data_q.shuffle();
	end
endmodule
```

# Write randomization constraints for the following requirements on an array.
An array of size 9 should contain any value from 1 to 9. Two values should be the same between indices 0 and 7.
```
module tb;
	bit [3:0] 	data_q [9];

	initial begin
		bit [2:0] idx_q [2];

		randomize(data_q, idx_q) with
		{
			// Let idx_q represent two random indices
			// which should contain same value
			unique { idx_q };
			solve idx_q before data_q;
	
			// When indices match, assign same value to data_q[i]
			// else follow general rule to keep between 1:9
			foreach (data_q[i]) {
				if (i == idx_q[1]) {
					data_q[i] == data_q[idx_q[0]];
				} else {
					data_q[i] inside {[1:9]};
				}
			}
		};

		$display ("idx_q  = %p", idx_q);
		$display ("data_q = %p", data_q);
	end

endmodule
```
