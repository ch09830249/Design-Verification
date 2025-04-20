## Simple Sequence
```
module tb;
  	bit a;
  	bit clk;

	// This sequence states that a should be high on every posedge clk
  	sequence s_a;
      @(posedge clk) a;
    endsequence

  	// When the above sequence is asserted, the assertion fails if 'a'
  	// is found to be not high on any posedge clk
  	assert property(s_a);


	always #10 clk = ~clk;

	initial begin
      for (int i = 0; i < 10; i++) begin
        a = $random;
        @(posedge clk);

        // Assertion is evaluated in the preponed region and
        // use $display to see the value of 'a' in that region
        $display("[%0t] a=%0d", $time, a);
      end
      #20 $finish;
    end
endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan 14 06:32 2020
[10] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 10ns failed at 10ns
	Offending 'a'
[30] a=1
[50] a=1
[70] a=1
[90] a=1
[110] a=1
[130] a=1
[150] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 150ns failed at 150ns
	Offending 'a'
[170] a=1
[190] a=1
$finish called from file "testbench.sv", line 27.
$finish at simulation time                  210
           V C S   S i m u l a t i o n   R e p o r t 
Time: 210 ns
```
![image](https://github.com/user-attachments/assets/14f5145d-745f-4003-8b9d-6becffacf522)  
## $rose
```
module tb;
  	bit a;
  	bit clk;

	// This sequence states that 'a' should rise on every posedge clk
  	sequence s_a;
      @(posedge clk) $rose(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// posedge 'a' is not found on every posedge clk
  	assert property(s_a);


	// Rest of the testbench stimulus
endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan 14 06:58 2020
[10] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 10ns failed at 10ns
	Offending '$rose(a)'
[30] a=1
[50] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 50ns failed at 50ns
	Offending '$rose(a)'
[70] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 70ns failed at 70ns
	Offending '$rose(a)'
[90] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 90ns failed at 90ns
	Offending '$rose(a)'
[110] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 110ns failed at 110ns
	Offending '$rose(a)'
[130] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 130ns failed at 130ns
	Offending '$rose(a)'
[150] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 150ns failed at 150ns
	Offending '$rose(a)'
[170] a=1
[190] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 190ns failed at 190ns
	Offending '$rose(a)'
$finish called from file "testbench.sv", line 27.
$finish at simulation time                  210
           V C S   S i m u l a t i o n   R e p o r t 
Time: 210 ns
```
![image](https://github.com/user-attachments/assets/886153f9-8927-4497-bca7-26c7571d0944)  
![image](https://github.com/user-attachments/assets/7feb7166-eb6a-4dc2-9281-a908c0f3bd6d)  
![image](https://github.com/user-attachments/assets/7bb468f1-a4d1-471c-8a3b-e80cea3a72aa)  

## $fell
```
module tb;
  	bit a;
  	bit clk;

	// This sequence states that 'a' should fall on every posedge clk
  	sequence s_a;
      @(posedge clk) $fell(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// negedge 'a' is not found on every posedge clk
  	assert property(s_a);


	// Rest of the testbench stimulus
endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan 14 07:09 2020
[10] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 10ns failed at 10ns
	Offending '$fell(a)'
[30] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 30ns failed at 30ns
	Offending '$fell(a)'
[50] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 50ns failed at 50ns
	Offending '$fell(a)'
[70] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 70ns failed at 70ns
	Offending '$fell(a)'
[90] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 90ns failed at 90ns
	Offending '$fell(a)'
[110] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 110ns failed at 110ns
	Offending '$fell(a)'
[130] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 130ns failed at 130ns
	Offending '$fell(a)'
[150] a=0
[170] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 170ns failed at 170ns
	Offending '$fell(a)'
[190] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 190ns failed at 190ns
	Offending '$fell(a)'
$finish called from file "testbench.sv", line 27.
$finish at simulation time                  210
           V C S   S i m u l a t i o n   R e p o r t 
Time: 210 ns
```
![image](https://github.com/user-attachments/assets/59396828-d169-49d1-ade5-4a4cb43d7e30)  
![image](https://github.com/user-attachments/assets/08d4c4c4-a2a1-4fbb-a37e-97ef7142d553)  
![image](https://github.com/user-attachments/assets/37a79782-d76d-4cb2-97e8-e32e7daea0a7)  

## $stable
```
module tb;
  	bit a;
  	bit clk;

	// This sequence states that 'a' should be stable on every clock
	// and should not have posedge/negedge at any posedge clk
  	sequence s_a;
      @(posedge clk) $stable(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// 'a' toggles at any posedge clk
  	assert property(s_a);


	// Rest of the testbench stimulus
endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan 14 07:12 2020
[10] a=0
[30] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 30ns failed at 30ns
	Offending '$stable(a)'
[50] a=1
[70] a=1
[90] a=1
[110] a=1
[130] a=1
[150] a=0
"testbench.sv", 12: tb.unnamed$$_0: started at 150ns failed at 150ns
	Offending '$stable(a)'
[170] a=1
"testbench.sv", 12: tb.unnamed$$_0: started at 170ns failed at 170ns
	Offending '$stable(a)'
[190] a=1
$finish called from file "testbench.sv", line 27.
$finish at simulation time                  210
           V C S   S i m u l a t i o n   R e p o r t 
Time: 210 ns
```
![image](https://github.com/user-attachments/assets/d1e8fc80-5b0e-4aef-aa8e-7c75ad4a11e5)  
![image](https://github.com/user-attachments/assets/c62d322c-37ef-4538-b73e-f5a558369de6)  
![image](https://github.com/user-attachments/assets/cc7972b2-d62b-40fb-92bc-9df97cd4fb97)  

