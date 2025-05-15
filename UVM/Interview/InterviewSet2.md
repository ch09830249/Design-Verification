# What is the difference between a deep copy and a shallow copy ?
A deep copy is one where nested class object contents are also entirely copied over into the new class object. A shallow copy is one where nested class objects are not copied but instead handles are simply assigned. So, if the original class object changes its contents, then the copied class also see the same contents.

# How to disable constraints?
All constraints are by default enabled and will be considered by the SystemVerilog constraint solver during randomization. A disabled constraint is not considered during randomization. Constraints can be enabled or disabled by constraint_mode().
```
class ABC;
	rand bit [3:0] 	data;

	constraint c_data { data == 10; }
endclass

ABC m_abc = new;
m_abc.c_data.constraint_mode(0); 	// Disable constraint
```

# Difference between code and functional coverage?
In Verilog/SystemVerilog, code coverage and functional coverage are two types of verification metrics used to measure the completeness of a testbench.

Code coverage measures the extent to which the testbench has exercised the RTL code being verified. It tracks which lines of the code were executed during simulation, which branches of conditional statements were taken, and which blocks of code were repeated in loops. Code coverage is often measured in terms of statement coverage, branch coverage, and condition coverage.

Functional coverage, on the other hand, measures the completeness of the functional requirements being verified. It tracks how many and which functional scenarios were exercised during simulation. Functional coverage is defined based on functional coverage points, which are specific items or aspects of the functional specification that need to be tested. For example, a functional coverage point could be the number of packets transmitted and received correctly by a network interface block.

The key differences between code coverage and functional coverage are:

Purpose: Code coverage is used to ensure that every line of code in the design has been tested while functional coverage is used to ensure that all functional requirements of the design have been tested.
Measurement: Code coverage is measured based on the number of lines of code executed, branches explored, and conditions evaluated during simulation, while functional coverage is measured based on the number of functional coverage points exercised during simulation.
Scope: Code coverage provides insight into the completeness of the implementation of the design, while functional coverage provides insight into the completeness of the specifications of the design.

# What is ignore_bins?
In SystemVerilog, ignore_bins is a keyword used in functional coverage to exclude certain bins from being counted towards the coverage goal.SystemVerilog certification

Ignoring bins can be useful when there are some bins that are not meaningful for the verification objectives, or if it is not feasible to cover some of the bins. By ignoring some bins, the coverage report can focus on the meaningful and feasible coverage points.

To ignore bins in a functional coverage point, the ignore_bins attribute can be used. Here's an example:
```
covergroup my_covergroup;
   // Coverage points definitions

	coverpoint my_var {
		bins  		zero 	= {0};
   		ignore_bins unused 	= {10};
	}

endgroup
```

# What are 2 state and 4 state variables? Provide some examples.
Two-state variables have only two possible values: 0 and 1. In two-state variables, there is no distinction between "unknown" and "floating" values. Two-state variables are commonly used in simple designs, or where the value of a variable is either known or unknown, but not floating.

Four-state variables, on the other hand, have four possible values: 0, 1, X, and Z. Four-state variables are used to model the behavior of digital circuits, where the signal can either be a known logic value, or a floating or unknown value.
```
reg [7:0] 	data_bus; 		// Can hold 0, 1, X, Z
bit  		true; 			// Can hold 0, 1
```


# How to ensure address range 0x2000 to 0x9000 is covered in simulations ?
To make sure that address ranges from 0x2000 to 0x9000 are covered in Verilog/SystemVerilog, we can use a covergroup to define coverage points for each address value within the range. Here's an example:
```
covergroup memory_access_coverage @(posedge clk);
   // Declare coverage points for each address within the range

   addr_coverage: coverpoint addr {
      bins addr_0x2000  		= {[16'h2000]};
      bins addr_0x2001_0x8FFF 	= {[16'h2001:16'h8FFF]};
      bins addr_0x9000  		= {[16'h9000]};
   }

   // Declare coverage points for other signals of interest
endgroup
```
Within the "addr_coverage" point, we declare three bins to cover the address range. The bin "addr_0x2000" covers the value 0x2000, while the bin "addr_0x2001_0x8FFF" covers the range from 0x2001 to 0x8FFF. Finally, the bin "addr_0x9000" covers the value 0x9000.

# What is layered architecture in Verification?
In verification, a layered architecture is a methodology in which the verification environment is structured into multiple layers of abstraction, each building on the lower layers. This approach separates functionality and responsibilities of different layers, making verification more manageable and scalable.

Layered architecture typically consists of three main layers:

Testbench layer: This is the top layer of the verification architecture, which contains test scenarios that stimulate the design under test (DUT) and verify its functionality. The testbench layer is responsible for test management, collecting and analyzing results, and reporting errors and warnings.
Verification IP (VIP) layer: The VIP layer provides hardware and software components that are reusable and pre-verified, such as memory models, bus functional models (BFMs), and protocol checkers. The VIP layer abstracts the DUT interface and behavior, allowing the testbench layer to focus on DUT functionality.
Functional block layer: This is the lowest layer of the verification architecture, which contains individual blocks of the design. The functional block layer specifies the behavior and function of the DUT at the RTL level. The functional block layer includes RTL code, gate-level models, and timing models.
The layered architecture approach promotes reusability and scalability of the verification environment. Each layer can be independently designed and tested, facilitating incremental verification of the DUT. It allows efficient and thorough testing for complex designs with multiple blocks, interfaces, and protocols. By separating concerns and providing abstraction, layered architecture makes verification more manageable and improves the quality of the design.

# Explain the cycle of verification and its closure.
In the context of digital design verification, the verification cycle refers to the iterative process of designing, developing, running tests, and debugging to ensure the design meets the functional and performance requirements. The verification cycle generally consists of design verification plan, testbench development, test execution and verification closure.

# Difference between dynamic array and queue
A dynamic array is a collection of similar data elements whose sizes and memory locations are allocated dynamically during the runtime of the program. The size of the array can be changed at runtime, making it more flexible than a static array.

It can grow or shrink dynamically.
It can be used for random access of data elements.
It does not have a fixed size.
It has an index to locate an element.
A queue is also a collection of similar data elements, but its primary function is to store and retrieve data elements in a specific order, FIFO (First in First out), or LILO (Last in Last out).

It is a sequential data structure that stores and retrieves elements in a specific order.
It follows the FIFO (First In First Out) or LILO (Last In Last Out) rule to maintain the order of elements.
It has two main functions of adding elements to the rear and removing elements from the front.

# Difference between structure and class
In object-oriented programming, both structures and classes can be used to define custom data types with properties and functions, but there are some differences in their behavior and usage.

Access Modifiers: Classes have private, public, and protected access modifiers for data members and member functions. Structures only support public access modifiers.
Inheritance: Classes support inheritance, where a new class can be derived from a base class. Structures do not support inheritance.
Constructors and Destructors: Classes have constructors and destructors that get called when objects are created and destroyed, respectively. On the other hand, structures do not have constructors or destructors.
Methods: Classes can have functions and tasks that operate on its members, but structures do not have them.
