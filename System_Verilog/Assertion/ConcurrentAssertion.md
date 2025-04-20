Concurrent assertions describe behavior that **spans over simulation time** and are **evaluated only at the occurence of a clock tick**.  
SystemVerilog concurrent assertion statements can be specified in a module, interface or program block running concurrently with other statements.  
Following are the properties of a concurrent assertion:  
* Test expression is evaluated **at clock edges based on values in sampled variables**
* Sampling of variables is done in the preponed region and evaluation of the expression is done in the observed region of the simulation scheduler.
* It can be placed in a procedural, module, interface, or program block
* It can be used in both dynamic and formal verification techniques
## Example 1
```
module tb;
    bit a, b;
    bit clk;

    always #10 clk = ~clk;

    initial begin
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            a <= $random;
            b <= $random;
            $display("[%0t] a=%0b b=%0b", $time, a, b);
        end
        #10 $finish;
    end

  // This assertion runs for entire duration of simulation
  // Ensure that both signals are high at posedge clk
  assert property (@(posedge clk) a & b);

endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Dec 11 14:46 2019
[10] a=0 b=0
testbench.sv", 24: tb.unnamed$$_4: started at 10ns failed at 10ns
	Offending '(a & b)'
[30] a=0 b=1
"testbench.sv", 24: tb.unnamed$$_4: started at 30ns failed at 30ns
	Offending '(a & b)'
[50] a=1 b=1
[70] a=1 b=1
[90] a=1 b=0
"testbench.sv", 24: tb.unnamed$$_4: started at 90ns failed at 90ns
	Offending '(a & b)'
[110] a=1 b=1
[130] a=0 b=1
"testbench.sv", 24: tb.unnamed$$_4: started at 130ns failed at 130ns
	Offending '(a & b)'
[150] a=1 b=0
"testbench.sv", 24: tb.unnamed$$_4: started at 150ns failed at 150ns
	Offending '(a & b)'
[170] a=1 b=0
"testbench.sv", 24: tb.unnamed$$_4: started at 170ns failed at 170ns
	Offending '(a & b)'
[190] a=1 b=0
"testbench.sv", 24: tb.unnamed$$_4: started at 190ns failed at 190ns
	Offending '(a & b)'
$finish called from file "testbench.sv", line 14.
$finish at simulation time                  200
```
![image](https://github.com/user-attachments/assets/68d0566f-ea3d-4c34-b61b-9f77017b42f1)  
## Example 2
```
module tb;
    bit a, b;
    bit clk;

    always #10 clk = ~clk;

    initial begin
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            a <= $random;
            b <= $random;
            $display("[%0t] a=%0b b=%0b", $time, a, b);
        end
        #10 $finish;
    end

  // This assertion runs for entire duration of simulation
  // Ensure that atleast 1 of the two signals is high on every clk
  assert property (@(posedge clk) a | b);

endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Dec 11 15:13 2019
[10] a=0 b=0
testbench.sv", 24: tb.unnamed$$_4: started at 10ns failed at 10ns
	Offending '(a | b)'
[30] a=0 b=1
[50] a=1 b=1
[70] a=1 b=1
[90] a=1 b=0
[110] a=1 b=1
[130] a=0 b=1
[150] a=1 b=0
[170] a=1 b=0
[190] a=1 b=0
$finish called from file "testbench.sv", line 14.
```
![image](https://github.com/user-attachments/assets/3e449e09-14f5-4dae-9bc9-ceea1395d1ca)  
## Example 3
```
module tb;
    bit a, b;
    bit clk;

    always #10 clk = ~clk;

    initial begin
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            a <= $random;
            b <= $random;
            $display("[%0t] a=%0b b=%0b", $time, a, b);
        end
        #10 $finish;
    end

  // This assertion runs for entire duration of simulation
  // Ensure that atleast 1 of the two signals is high on every clk
  assert property (@(posedge clk) !(!a ^ b));    // XNOR 

endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Dec 11 15:26 2019
[10] a=0 b=0
"testbench.sv", 24: tb.unnamed$$_4: started at 10ns failed at 10ns
	Offending '(!((!a) ^ b))'
[30] a=0 b=1
[50] a=1 b=1
"testbench.sv", 24: tb.unnamed$$_4: started at 50ns failed at 50ns
	Offending '(!((!a) ^ b))'
[70] a=1 b=1
"testbench.sv", 24: tb.unnamed$$_4: started at 70ns failed at 70ns
	Offending '(!((!a) ^ b))'
[90] a=1 b=0
[110] a=1 b=1
"testbench.sv", 24: tb.unnamed$$_4: started at 110ns failed at 110ns
	Offending '(!((!a) ^ b))'
[130] a=0 b=1
[150] a=1 b=0
[170] a=1 b=0
[190] a=1 b=0
$finish called from file "testbench.sv", line 14.
$finish at simulation time                  200
```
![image](https://github.com/user-attachments/assets/37000a48-6b96-4fcc-9fea-0503e3e87919)  
