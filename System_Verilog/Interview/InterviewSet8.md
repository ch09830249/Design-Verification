# Why can't program blocks have an always block in them ?
An always block is a concurrent process that runs forever and gets triggered based on changes to signals in the sensitivity list. A program block is intended to be a testcase that applies stimulus to the DUT and finish at some point in time. Having an always block will stall the program from coming to an end and hence it doesn't make sense to include it in a program block.

# What are in-line constraints?
In-line constraints are a way to specify constraints directly when randomized.
```
bit [7:0] 	data;

std::randomize(data) with { data > 7; }; 	// in-line constraint
```

# What are the advantages of cross-coverage?
Cross-coverage is a type of coverage measurement in SystemVerilog that combines coverage data for two or more variables or conditions. Here are some of the advantages of using cross-coverage:
Better coverage granularity: Cross-coverage allows the user to define more specific coverage goals that combine multiple variables, instead of relying on individual coverage points. This provides better visibility into the overall behavior of the design, and helps to identify corner cases or unexpected interactions.
Reduced verification effort: By combining coverage data for multiple variables or conditions, cross-coverage reduces the number of individual coverage points that need to be tested. This can save verification time and effort, especially for complex designs with many variables or conditions.
Improved result analysis: Cross-coverage generates more detailed coverage reports that show the correlation between different variables or conditions. This helps the user to identify patterns or trends in the data, and to perform more targeted verification activities.

# What are constraints?
SystemVerilog constraints are used to control the values that are randomized for variables during simulation.  
Constraints provide a way to **specify the valid range of values for a variable**, as well as **any relationships or conditions between variables**.  
```
rand bit [7:0]  data;

constraint myConstraint
{
	data inside {[0:10]};
}
```

# How can we display hex values of a variable in uppercase ?
$display format specifier can have %h or %H , and quite intuitively we assume that the latter is used to display it in uppercase. However, that is not the case and we need a workaround.
```
bit [31:0] y = 32'hCAFE_4BED;
string str;

str.hextoa(y);
$display(str.toupper);
```

# Constrain a dynamic array such that it does not pick values from another array.
```
module tb;
	bit [3:0] 	da [];
	bit [3:0] 	myq [$];

	initial begin
		repeat (10) myq.push_back($random);

		std::randomize (da) with
		{
			da.size == 10;
			foreach (da[i]) { ! (da inside {myq}); }
		};
	end
endmodule
```

# What is the output for the following code ?
```
initial begin
	byte loop = 5;

	repeat (loop) begin
		$display("hello");
		loop -= 1;
	end
end
```
The repeat loop iterates a fixed number of times and the iteration count cannot be changed once in the loop. The output will be:
```
hello
hello
hello
hello
hello
```

# What is the difference between overriding and overloading?
* Overriding refers to the process of **providing a new implementation for an inherited method in a subclass**. In other words, if a superclass defines a method, a subclass can override that method by providing its own implementation. When the subclass object calls the overridden method, **the new implementation in the subclass is executed instead of the original implementation in superclass**.
  * The **signature (name, return type, and parameters) of the method remains the same**.
  * The main purpose of method overriding is to **implement a different behavior of the same method in a subclass**.

* Overloading refers to **defining multiple methods within the same class that have the same name but different parameters (就是 function name 相同, 但是 signature 不同)**. This allows the same method name to be used for different operations. When the method is called, the system automatically selects the appropriate version of the method based on the parameters passed. The signature of the method is different in each overload due to the differing number or types of arguments.

# What are the different types of verification approaches?
There are multiple types of verification approaches like **simulation based verification**, **formal verification**, **emulation or FPGA prototyping**.

# What is the difference between always_comb() and always@(*)?
always_comb is automatically triggered once at time zero, after all initial and always procedures have been started, whereas always @ (*) will be triggered first when any signal in the sensitivity list changes.  
always_comb is sensitive to changes of contents in a function where the latter is sensitive only to the arguments of the function when invoked inside it.  
always_comb cannot have statements that have delays or timing constructs in it.  
Variables used on the LHS inside an always_comb block cannot be assigned to in any other parallel process.

Verilog 中我們會使用 always 來建立一個 block。這個語法其實沒有太大的問題，而 SystemVerilog 提供了數個更好的語法。
SystemVerilog 中引入了 always_comb always_ff 用來提供替換原本的 always，分別用在 combinational circuit 以及 register 使用。
使用這兩個語法的話，如果 tool 支援的話，可以在不小心把 register 跟 combinational circuit 寫錯的時候，發出一些警告。tool 不支援的話也能多少當作註解來用。

## always_comb
在最早的 Verilog 裡面，combinational circuit 需要用 @ 語法加上 sensitive list 才能正確運作。然而隨語法的更新，根本沒有這個需求了，所以在 Verilog 中 always 後面一律是 @(*)。
```
always@(*) begin
   x = y;
end
```
這就導致了 @(*) 看起來很多餘，所以新版語法 always_comb 就直接去掉了，如下：
```
always_comb begin
   x = y;
end
```
另外，因為不用加上 @(*)，所以想把他當 assign 來用也是可以的。
```
assign x = y;
always_comb x = y;
```
## always_ff
這個語法相比 always_comb 沒什麼好說，因為就是直接替換掉本來的 always 就好。
```
always_ff@(posedge clk) begin
   x <= y;
end
```
最後，雖然也有 always_latch 這個語法用在 latch 的，但是在大部分同步電路中，這個不太常用，所以沒有介紹
