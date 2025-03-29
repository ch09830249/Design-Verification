# What is a SystemVerilog interface ?
SystemVerilog interfaces are a way to create structured hierarchical connections between modules and blocks in a design. They provide a way to bundle signals and functionality into reusable components, which can be easily instantiated and connected in a design.

Modular design: Interfaces provide a modular approach to design, making it easier to create and reuse building blocks in a system.
Encapsulation: They help in encapsulating the functionality and signals inside a module or block, making it easier to understand and maintain.
Configurability: Interfaces can be parameterized, allowing for easy configurability and scalability.

# Difference between reg and logic.
Both reg and logic are used to store 4-state logic values that can be referenced later.  
The main difference is that logic signals can be used in both procedural and continuous assignments whereas reg can only be used in procedural code.

# Difference between :/ and := operators in randomization
Both operators are used in distribution constraints to assign weightage to different values in the distribution.

The :/ operator assigns the specified weight to the item, or if the item is a range, then the weight of each value is divided by N. The := operator assigns the specified weight to the item or if the item is a range, then to every value value in the range.

# How to disable randomization?
Randomization of variables can be disabled with rand_mode.
```
class ABC;
	rand bit [3:0] data;
endclass

module tb;
	initial begin
		ABC m_abc = new;
		m_abc.data.rand_mode(0); 	// Disable randomization

		m_abc.data.rand_mode(1); 	// Enable randomization
	end
endmodule
```

# Different types of code coverage.
Code coverage is a metric used to measure how well tests have exercised the design under test. It typically reports on the percentage of execution achieved across various dimensions of the design, such as statements, branches, and expressions, toggle, assertions and FSM.

# Write a constraint to detect odd numbers of ones in an 8-bit sequence.
Here's an example constraint that detects odd numbers of ones in an 8-bit sequence:
```
class ABC;
  rand bit [7:0] data;

  constraint c_data { $countones(data) % 2 != 0; }
endclass

module tb;
  initial begin
    ABC m_abc = new;

    for (byte i = 0; i < 20; i++) begin
      m_abc.randomize();
      $display("data = 0b%0b", m_abc.data);
    end
  end
endmodule
```

# What are local and protected access qualifiers?
A class member declared as local is available only to methods inside the class and are not visible within subclasses.
A class member declared as protected is available to methods inside the class and also to methods within subclasses.

# How does OOP concepts help in verification ?
Modular Design: Each module/class represents different aspects of the design. As a result, it becomes easier to develop a test bench by reusing and integrating these modular components. This saves time and effort in developing test cases and makes the system more scalable.
Encapsulation: Operations performed on any data object can be defined within the same class. For example, a function to pack a data array into a stream of 64 bit data.
Inheritance: Allows to create a base class and extend it with further derived classes. Common properties and methods are usually defined in base classes so that all subclasses have access and hence avoid code duplication
Polymorphism: Allows different implementations of the same method or function. Polymorphism helps to implement alternate test case scenarios without affecting the rest of the code significantly.

# What is a virtual interface ?
An interface is a collection of signals that allow connections to the DUT from the testbench. The handle to this interface is made available in classes by making it virtual. Hence a virtual interface is nothing but a handle that can hold a reference to the actual interface. Remember that an interface is declared at the testbench top level so that it can be passed to the DUT. So, rest of the components get access to this interface via a virtual interface.
```
class wishbone_monitor;
	virtual wishbone_if 	m_vif; 	// A virtual interface handle

	virtual task monitor;
		forever begin
			@(m_vif.clk);
			// Rest of the code
		end
	endtask
endclass
```

# Why logic was introduced in SV?
**logic is a new SystemVerilog data type**, when compared to Verilog which can be used in place of reg and wire in both procedural blocks and continuous assignments. (reg 用於 procedural blocks, wire 則是連續賦值)
logic 可以直接取代這兩個 data type, 放在 procedure block 內或是連續賦值皆可
It removes the hassle of having to redefine an existing signal as reg or wire depending on where it is used.