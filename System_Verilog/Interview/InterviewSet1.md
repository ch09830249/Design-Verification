# 標題字
## 次標題字
###### 小標題字
```
程式區塊
```
**粗體**
_斜體_  
~刪除線~  
* Item 1
* Item 2
  * Item 2a
  * Item 2b
- [x] This is a complete item
- [ ] This is an incomplete item  
`小區塊語法`  
> Quote one sentences
>>Quote two sentences
>>Quote two sentences
>>>Quote three sentences

  Testing the functionality of interrupts using functional coverage involves the following steps:

Define functional coverage goals: First, you need to define your functional coverage goals. These goals should be specific to the interrupts you want to test. For example, you might define goals for interrupt latency, interrupt frequency, or interrupt priority handling.
Create a testbench for interrupts: Next, you need to create a testbench that generates interrupts with different characteristics. This testbench should also monitor the behavior of the design under test (DUT) in response to the interrupts.
Implement functional coverage: You can then implement functional coverage in your testbench to track how often each of the defined functional goals is achieved. You can use standard SystemVerilog constructs like covergroups, coverpoints, and bins to define and track the functional coverage.
Analyze the functional coverage results: Finally, you can analyze the functional coverage results to determine how well your testbench tests the desired interrupt functionality. Based on the results, you can make adjustments to your testbench to improve the tests.
The scope resolution operator in SystemVerilog is denoted by the double colon '::' symbol. The basic purpose of this operator is to specify the scope in which an identifier is defined or should be searched for.

Here are some common uses of the scope resolution operator:SystemVerilog certification

Accessing variables or modules within a hierarchy: When a design has a hierarchy of modules or sub-modules, the scope resolution operator can be used to access variables or modules that are defined in different scopes. For example, if a variable 'clk' is defined in a top-level module and is used in a lower-level module, then we use the scope resolution operator to specify the scope of 'clk'.
Resolving naming conflicts: When a design has two or more variables or modules with the same name, the scope resolution operator can be used to differentiate the variables or modules by specifying their scope.
package ahb_pkg;
	typedef enum {READ, WRITE} e_access;
endpackage

package wishbone_pkg;
	typedef enum {WRITE, READ} e_access;
endpackage

ahb_pkg::e_access 	m_access; 		// m_access = 1 indicates WRITE
Accessing static variables and functions: The scope resolution operator is also used to access static properties and methods in a class.
Accessing items in package: Elements in a package can be imported using import with scope resolution operator.
import ahb_pkg::*; 	 		// Imports everything in the package called "ahb_pkg"
import enum_pkg::global; 	// Imports everything under "global" from enum_pkg
Read more on SystemVerilog Scope Resolution Operator.

SystemVerilog certification
The randc keyword in SystemVerilog will first exhaust all combinations possible before repeating a value. This is different from rand keyword where the same value may repeat even before all combinations are exercised.

Here's an example :

class ABC;
	rand 	bit [1:0] 	x; 		// randomization can give x = 3, 1, 1, 0, 3, 0, 2, 2
	randc 	bit [1:0] 	y; 		// randomization can give y = 1, 3, 0, 2, 3, 1, 2, 0
endclass
Read more on SystemVerilog rand Variables.

Inheritance is a concept in object-oriented programming that allows creating a new class by inheriting or extending the properties and behavior of an existing class. The existing class is called the parent or base class, and the new class is called the child or derived class. The child class inherits all the members of the parent class, such as variables, methods, and constructors, and can also add new members or override the inherited members.

Read more on SystemVerilog Inheritance.

DPI stands for Direct Programming Interface, which is a mechanism in SystemVerilog for integrating SystemVerilog design and verification code with external C/C++ code. It enables interoperability between SystemVerilog and other high-level programming languages, which is not possible with traditional Verilog.

DPI export is used to export C/C++ functions to SystemVerilog. This means that a C/C++ function can be used as a task or function in SystemVerilog by creating an import task or import function.

extern "C" void my_function(int arg1, int arg2) {
	// Do something here
}
And here's an example of how to import this function in SystemVerilog using DPI import:

import "DPI-C" context function void my_function(int arg1, int arg2);
# fork join, fork join_any, fork join_none 的差異

Semaphore is a synchronization mechanism used to control access to shared resources. It is a variable or an abstract data type that is used to indicate the status of a shared resource, whether it is free, in use, or unavailable.

In a multi-tasking or multi-threaded environment where multiple processes or threads access shared resources concurrently, semaphores can ensure that only one process or thread can access the shared resource at a time. This helps to avoid conflicts and data inconsistency caused by simultaneous access, which could result in unexpected behavior.

# fork join, fork join_any, fork join_none 的差異

They are all used to spawn processes in parallel.

fork-join will exit only after all child processes finish.
fork-join_any will exit after any of the child processes finish.
fork-join_none will exit immediately without waiting for any child process to finish.
See examples of fork join, fork join_any and fork join_none.
# static variable 和 automatic variable 的差異
The main difference is that a static variable gets initialized once before time 0 at some memory location and future accesses to this variable from different threads or processes access the same memory location. However, an automatic variable gets initialized every time the scope where it is declared gets executed and stored in a different location every time.

# Module 和 Program block 的差異

A module is the primary container for all RTL design code and allows hierarchical structuring of design intent. A program block on the other hand is a verification container introduced in SystemVerilog to avoid race conditions in the testbench by executing its contents at the end of the time step.

# Dynamic array 和 Associative array 的差異
A dynamic array is an array whose size can be changed during runtime. Elements of the array are stored in a contiguous block of memory, and the size is determined when the array is created. An associative array, on the other hand, is also known as a dictionary or a map. It is a collection of key-value pairs where each key has a corresponding value.

In a dynamic array, the elements are accessed using an index, which refers to the position of the element in the array. In an associative array, elements are accessed using the key.

# Race condition in SV
![484633121_1026278449403756_1107950053659493403_n](https://github.com/user-attachments/assets/56d70134-378a-413f-89c9-a270a283ac85)
