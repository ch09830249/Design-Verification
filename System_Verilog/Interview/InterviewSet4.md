# Is it possible to override existing constraints?
Yes, it's possible to override existing constraints in SystemVerilog using **inline constraints** or **inheritance**.
```
class ABC;
	rand bit [3:0] data;

	constraint c_data { data inside {[5:10]}; }
endclass

module tb;
	initial begin
		ABC abc = new;

		// Use inline constraint to override with new value
		// Note that this should not contradict the hard constraints in ABC
		abc.randomize() with { data == 8; };
	end
endmodule
```
Another way is to redefine constraint block in an inherited class.
```
class DEF extends ABC;
	constraint c_data { data inside {[0:5]}; }   // 記得 constraint 名稱也要相同
endclass

module tb;
	initial begin
		DEF def = new;
		def.randomize();
	end
endmodule
```

# What will be your approach if functional coverage is 100% but code coverage is too low ?
If the functional coverage is 100% but the code coverage is too low, it typically means that there are parts of the code that are never executed and therefore not covered by the test cases. Here are some possible approaches to improve code coverage:

Review the code and identify the uncovered areas: You can go through the code manually or use a code coverage tool to identify the parts of the code that are not covered by the tests. This will help you to focus on the areas that need to be tested more thoroughly.
Add new test cases: Once you have identified the uncovered areas, you can add new test cases to cover them. You can use different techniques such as random testing, directed testing or assertion-based testing to create new test cases.
Modify existing test cases: You can also modify the existing test cases to cover the uncovered areas. For example, you can change the parameters or stimuli of the test cases to target specific areas of the code.
Use code coverage metrics: You can use code coverage metrics as a guide to track your progress and ensure that you are improving overall coverage. You can set targets for specific types of coverage, such as branch or statement coverage, and monitor your progress as you add new test cases or modify existing ones.
Use techniques like coverage-driven verification and constrained-random testing: These techniques focus on generating test cases to cover specific portions of the design, which can help you achieve better code coverage.

# What are the types of assertions?
Assertions are statements that specify a particular relationship between two or more signals or variables. There are two main types of assertions, which are as follows:

Immediate assertion: Checks whether a particular condition is true at a particular point in time.
Concurrent assertion: Checks whether a particular condition is always true over a period of time.

# How to find indices associated with associative array items?
Array manipulation functions can be used to query indices and values in SystemVerilog arrays.
```
module tb;
  int   fruit_hash [string];
  string 	idx_q [$];

  initial begin
    fruit_hash["apple"] = 5;
    fruit_hash["pear"]  = 3;
    fruit_hash["mango"] = 9;

    idx_q = fruit_hash.find_index with (1);
    $display("idx_q= %p", idx_q);
  end
endmodule

// Output
// idx_q= '{"apple", "mango", "pear"}
```

# Give an example of a function call inside a constraint.
**The function must return a value** that can be used in the constraint expression. Here's an example:
```
function int rand_range(int a, int b);
    return (a + b) % 2;
endfunction

class ABC;
    rand bit my_val;

    constraint my_val_c {
        my_val == rand_range(a, b);
    }
endmodule
```

# What are pass-by-value and pass-by-reference methods?
Pass-by-value and pass-by-reference are two ways of passing arguments to a function or a method in programming languages.

In **pass-by-value** method, **a copy of the value of the argument is passed to the function or method**. Any change made to the value inside the function or method **does not affect the original value** of the argument.
```
function void abc(int a, b);
```
In **pass-by-reference** method, **a reference to the memory location of the argument is passed to the function or method**. Any changes made to the value inside the function or method **will affect the original value** of the argument.
```
function void abc(ref int a, b);
```

# Difference between initial and final block
The initial block is executed at the start of simulation, i.e. at time 0 units. This is useful for initializing variables and stting up initial configurations. This is the very basic procedural construct supported since the first version of Verilog.

However, the final block was introduced in SystemVerilog and is executed just before the simulation ends. This does not consume any time and hence is very ideal to do last minute housekeeping tasks and print reports.

# What are the default values of variables in the SystemVerilog ?
* The default value of all
  * 2-state variables are zero, and
  * 4-state variables are X.
  * Inputs that are not connected are Z.

# What is polymorphism and its advantages?
Polymorphism is a fundamental concept in object-oriented programming that allows objects of different classes to be treated as if they are objects of the same class.

The advantages of polymorphism in object-oriented programming are:

Code reusability: Polymorphism enables code reuse, as objects of different classes can be treated as if they are objects of the same class. This means that common behaviors and methods can be defined in a superclass and inherited by multiple subclasses.
Flexibility and extensibility: Polymorphism allows objects to behave differently based on the context in which they are called, improving the flexibility of the code. It also enables extensibility by allowing new subclasses to be added to a program easily without modifying the existing code.
Code readability and maintainability: Polymorphism can improve the readability and maintainability of the code by reducing the amount of redundant code and making it easier to understand the relationship between different classes.

# What is the purpose of this pointer in SystemVerilog ?
The this keyword is used to **explicity reference the current class object**.  
This is mostly **used within class definitions** to be able to specifically reference variables and methods belonging to the same class.
有時候 local variable 和 class member 同名時, 避免誤用所以加上 this
