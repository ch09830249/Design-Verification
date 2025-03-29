# 甚麼是 Semaphore 且何時需要使用它?
  Testing the functionality of interrupts using functional coverage involves the following steps:
Define functional coverage goals: First, you need to define your functional coverage goals. These goals should be specific to the interrupts you want to test. For example, you might define goals for interrupt latency, interrupt frequency, or interrupt priority handling.
Create a testbench for interrupts: Next, you need to create a testbench that generates interrupts with different characteristics. This testbench should also monitor the behavior of the design under test (DUT) in response to the interrupts.
Implement functional coverage: You can then implement functional coverage in your testbench to track how often each of the defined functional goals is achieved. You can use standard SystemVerilog constructs like covergroups, coverpoints, and bins to define and track the functional coverage.
Analyze the functional coverage results: Finally, you can analyze the functional coverage results to determine how well your testbench tests the desired interrupt functionality. Based on the results, you can make adjustments to your testbench to improve the tests.

# 甚麼是 Semaphore 且何時需要使用它?
The scope resolution operator in SystemVerilog is denoted by the double colon '::' symbol. The basic purpose of this operator is to specify the scope in which an identifier is defined or should be searched for.
Here are some common uses of the scope resolution operator:
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

# 如何使用 randc in SV?

The randc keyword in SystemVerilog will first exhaust all combinations possible before repeating a value. This is different from rand keyword where the same value may repeat even before all combinations are exercised.
Here's an example :
class ABC;
	rand 	bit [1:0] 	x; 		// randomization can give x = 3, 1, 1, 0, 3, 0, 2, 2
	randc 	bit [1:0] 	y; 		// randomization can give y = 1, 3, 0, 2, 3, 1, 2, 0
endclass

# 甚麼是 Inheritance?
繼承是物件導向程式設計中的一個概念，允許透過繼承或擴展現有類別的屬性和行為來建立新類別。
現有的類稱為父類或基類，新擴展出來的類別稱為子類或衍生類。子類別繼承了父類別的所有成員，如變量，方法和建構函數，也可以新增成員或覆寫繼承的成員。

# 甚麼是 DPI? 解釋 DPI export import
DPI stands for Direct Programming Interface, which is a mechanism in SystemVerilog for integrating SystemVerilog design and verification code with external C/C++ code. It enables interoperability between SystemVerilog and other high-level programming languages, which is not possible with traditional Verilog.
DPI export is used to export C/C++ functions to SystemVerilog. This means that a C/C++ function can be used as a task or function in SystemVerilog by creating an import task or import function.
extern "C" void my_function(int arg1, int arg2) {
	// Do something here
}
And here's an example of how to import this function in SystemVerilog using DPI import:
import "DPI-C" context function void my_function(int arg1, int arg2);

# What is the advantage of seed in randomization?
In SystemVerilog, seed is used as a starting point or initial value for the random number generator. The advantage of using the seed in randomization is that it allows for a more deterministic and reproducible behavior of the randomized simulation.

By setting a seed, a specific set of randomized values can be generated consistently, making it easier to replicate specific test scenarios and debug issues that arise during simulation. It also allows for better verification of the design as specific tests can be rerun with the same seed to ensure that issues have been resolved and that the behavior of the design is as expected.

# Is it possible to write assertions in class?
Yes, assertions using assert and assume are used to check the correctness of the design, and they can be written in any of the SystemVerilog constructs including modules, interfaces, programs or classes.

In SystemVerilog, assertions can be written using the assert and assume keywords. These keywords can be used directly inside a SystemVerilog class, with the assertion check being triggered when the appropriate method of the class is called.

# What is a clocking block?
A clocking block is a SystemVerilog construct that provides a way to model clock-related events that occur in a design. It is specifically used to define the timing and synchronization of signals that are driven by a clock. The clocking block can be used to drive and sample signals using the clock signal, with the signals being synchronized at specific edges of the clock.  
clocking block是為了避免test bench跟DUT搶訊號造成race condition
![image](https://github.com/user-attachments/assets/b910b4ec-1eb0-40a0-9a02-128628d29ca1)

# What is an abstract class?
An abstract class is a class in object-oriented programming that cannot be instantiated, meaning it cannot be used to create objects.  
虛擬類別是不能被實例化的, 有點像是建立 class 的 prototype
Instead, it is used as a superclass to other classes, providing a common set of properties and methods that subclasses can inherit and implement as necessary.
虛擬類別提供一些通用的 properties 和供子類繼承並需要實作的 method

# How to disable a cover point?
Covergroups and coverpoint weight can be disabled by setting its weight to zero.	設定該 cover group 或 cover point 的權重為 0 即可
```
covergroup cg_ahb @ (posedge hclk);
	cp_haddr  : coverpoint haddr;
	cp_htrans : coverpoint htrans;
	...
endgroup

cg_ahb m_cg_ahb = new();
m_cg_ahb.cp_htrans.option.weight = 0;  // disable coverpoint by setting weight to 0
```

# What is super keyword?
The super keyword in SystemVerilog or even any OOP language refers to the superclass of a class. 
**It is used to access methods and variables of the superclass from within a subclass. 在子 class 透過 super 來取用父 class 的 method 和 variabless**

