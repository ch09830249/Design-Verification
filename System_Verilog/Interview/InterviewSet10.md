# What is SVA?
SVA or SystemVerilog Assertions provides a syntax for expressing assertions that describe the expected behavior of a design, allowing for direct verification of its correctness.

Assertions expressed using SVA can be used to verify various types of design properties, such as proper data flow, correct timing constraints, and correct synchronization between different parts of the design. SVA can be used as a standalone language or in conjunction with other formal verification techniques such as model checking and theorem proving. It is an important tool for ensuring the correctness and reliability of digital designs in VLSI and other fields.

# When you will say that verification is completed?
Verification is typically considered complete when all the specified verification goals and requirements have been met and demonstrated through testing and analysis of the design. This means that all of the verification tests have been run and that the design has passed all of the necessary functional and performance requirements. Verification is a continuous process that starts early in the design cycle and continues until the final stages of the design and development process. Throughout this process, different verification techniques and methodologies are used to ensure that the design is free from errors.

Verification completeness is typically determined using a set of predefined metrics and criteria that are used to evaluate the overall quality and reliability of the design. Such metrics may include functional coverage, code coverage, and timing analysis. Ultimately, the decision to declare verification complete is based on the verification team's confidence in the design's functionality and reliability to be used in the intended application and environment.

# What are system tasks?
System tasks are **pre-defined functions or built-in functions** in SystemVerilog that are used to execute certain tasks related to the simulation and verification of a design.  
Some common system tasks in SystemVerilog include:  
**$display**: Used to display formatted output to the console or log file.  
**$time**: Used to retrieve simulation time and wall-clock time, respectively.  
**$finish**: Used to end the simulation after a specific amount of time or when a specific condition is met.  
**$random**: Used to generate random values for variables or signals.  

# Which array type is perferred for memory declaration and why?
The preferred array type for memory declaration is an **associative array** because it is more efficient in storing data at random address locations.  
It does not require all addresses in memory to be pre-allocated before usage unlike a dynamic array.

# What is the advantage of seed in randomization?
seed is used as a starting point or initial value for the random number generator. 
The advantage of using the seed in randomization is that it allows for a more deterministic and reproducible behavior of the randomized simulation.  
By setting a seed, a specific set of randomized values can be generated consistently, making it easier to replicate specific test scenarios and debug issues that arise during simulation.  
同樣的 seed 會產生相同的隨機序列, 故可以複製相同的行為  
It also allows for better verification of the design as specific tests can be rerun with the same seed to ensure that issues have been resolved and that the behavior of the design is as expected.
```
class packet;
    rand bit [31:0] src, dst, data[8];
    randc bit [7:0] kind;

    constraint c {
        src >10;
        src <15;
    }
endclass

//----------------------------------

Packet p;
initial begin
    p = new();
    p.srandom(100);
    //assert 保證 randomize 成功，否則報 fatal（如果 constraint 有衝突的話，如 src>15 and src<10 則會 random 失敗）
    assert (p.randomize()) else $fatal(0, "Packet::randomize failed");
end
```

# Is it possible to write assertions in class?
Yes, assertions using assert and assume are used to check the correctness of the design, and they can be written in any of the SystemVerilog constructs including modules, interfaces, programs or classes.

In SystemVerilog, assertions can be written using the assert and assume keywords. These keywords can be used directly inside a SystemVerilog class, with the assertion check being triggered when the appropriate method of the class is called.

# What is a clocking block?
A clocking block is a SystemVerilog construct that provides a way to model clock-related events that occur in a design.  
It is specifically used to define the timing and synchronization of signals that are driven by a clock.  
The clocking block can be used to drive and sample signals using the clock signal, with the signals being synchronized at specific edges of the clock.  
clocking block 是為了避免 test bench 跟 DUT 搶訊號造成 race condition
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

