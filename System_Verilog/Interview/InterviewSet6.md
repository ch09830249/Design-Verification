# Write a small function to push 10 unique values from 0 to 50 into a queue.
```
function random();
	bit [7:0] array[$];	// 每個 element 8 bits

	for (int i = 0; i  10; i++) begin
		int num;
		std::randomize(num) with
		{
                  num inside {[0:50]};	// num 範圍 0~50
		  !(num inside {array}; // 且之前沒有產生過
		};
		array.push_back(num);	// 推進 array
	end
endfunction
```

# Write constraints to randomize with the following requirements.
Assume memory region from 0x0 to 0x100. There is a small region in between from 0x20 to 0xE0 that is reserved. Write system verilog constraints to choose a block of memory of size 16 bytes that is outside the reserved region and inside the entire memory range. The starting address of the block should be 4-byte aligned.
```
rand bit [31:0] 	addr;
int 			size = 'h10;

constraint c_addr
{
	addr inside {[0:'h100]};      	// Ensure its within memory region
	!(addr inside {['h20:'hE0]}; 	// Ensure its not in reserved region
	addr % 4 == 0; 					// Ensure its 4-byte aligned
	addr + size inside {[0:'h20], ['hE0:'h100]}; 	// Ensure its either in lower or upper region
	!(addr + size inside {'h20, 'h100}); 		// Ensure last addr does not hit limit
}
```

# Write constraints to randomize with the following requirements.
Assume a memory region exists from 0x2000 to 0x4000 that is byte addressable. Write SV constraints to randomly pick an address within this memory region that is aligned to 4-byte boundary.
```
bit [31:0] 		addr;
constraint c_addr
{
	addr inside {[32'h2000:32'h4000]};
	addr % 4 == 0;
	//  addr[1:0] == 0;  	Also okay
}
```

# Provide solution for the following requirement.
Assume a class called "ABC" has been used throughout in a project. In a derivative project, you had to extend "ABC" to form "DEF" and add some more variables and functions within it. What will happen if you try to use an object of "ABC" that was created in the legacy testbench to access these new variables or functions ?

It will result in a compilation error because the new variables do not exist in the base class. Instead you need to declare a local variable of type "DEF" and perform a dynamic cast if required to access the new variables and functions.

# Randomly generate 8, 16, 32, 64 with equal probability using SystemVerilog constructs.
```
module tb;
	initial begin
		bit [31:0] result;
		result = 1 << $urandom_range(3, 6);	// 左移 3~6 bits
	end
endmodule
```

# What is the difference between mailbox and queue ?
A queue is a variable size ordered collection of elements of the same type.

A mailbox is a communication mechanism used by testbench components to send a data message from one to another.  
A mailbox has to be parameterized to hold a particular element and can be either bounded or unbounded. 
It can also suspend the thread by tasks like get() and put(). So a component can wait until an item is available in the mailbox.

# What is the difference between rand and randc ?
* **rand** randomizes the variable and **can have repetitive values** before the entire set of allowable values are used.	可重複產生之前產生過的值
  * For example, a 2-bit variable when used with rand can give values 1, 3, 3, 2, 1, 3, 0  
* **randc** randomizes the variable and **repeats a value only after the entire set of allowable values are used**.		之前產生過的值不會再次產生, 直到所有可能的數值都產生過後
  * For example, a 2-bit variable when used with randc can give values [1, 3, 2, 0], [0, 3, 1, 2], 1 ...  
    The values in the square brackets show a set.

# How can we reference variables and methods defined in the parent class from a child class ?
The **super keyword** is used to access variables and methods of the parent class and is a very basic construct of OOP.

# Where is extern keyword used ?
An extern keyword is used to **define methods and constraints outside the class definition**.  
For example, we could have the declaration of functions and constraints within the class body, but do the complete definition later on outside the class body.
```
class ABC;

  // Let this function be declared here and defined later
  // by "extern" qualifier
  extern function void display();

endclass

// Outside the class body, we have the implementation of the
// function declared as "extern"
function void ABC::display();

   $display ("Hello world");

endfunction

module tb;

  // Lets simply create a class object and call the display method
  initial begin
    ABC abc = new();
    abc.display();
  end
endmodule
```

# Give one way to avoid race conditions between DUT and testbench in a verification environment
Clock edges are the most probable points for a race condition to arise. The DUT may sample one value but the testbench may sample something else.

Although race conditions may arise from improper coding practices, use of SystemVerilog Clocking Blocks allows the testbench to sample DUT appropriately and drive inputs to the DUT with a small skew. Also, this allows the skews to be changed later on with minimal code change.

Race condition can also be avoided by the use of program blocks and the use of non-blocking assigments.
