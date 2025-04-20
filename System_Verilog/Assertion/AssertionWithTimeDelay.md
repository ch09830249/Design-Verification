```
module tb;
  bit a, b;
  bit clk;

  // This is a sequence that says 'b' should be high 2 clocks after
  // 'a' is found high. The sequence is checked on every positive
  // edge of the clock which ultimately ends up having multiple
  // assertions running in parallel since they all span for more
  // than a single clock cycle.
  sequence s_ab;
    @(posedge clk) a ##2 b;
  endsequence

  // Print a display statement if the assertion passed
  assert property(s_ab)
  	$display ("[%0t] Assertion passed !", $time);

  always #10 clk = ~clk;

  initial begin
    for (int i = 0; i < 10; i++) begin
      @(posedge clk);
      a <= $random;
      b <= $random;

      $display("[%0t] a=%b b=%b", $time, a, b);
    end

    #20 $finish;
  end
endmodule
```
```
Compiler version P-2019.06-1; Runtime version P-2019.06-1;  Jan 16 06:49 2020
[10] a=0 b=0
"testbench.sv", 14: tb.unnamed$$_0: started at 10ns failed at 10ns
	Offending 'a'
[30] a=0 b=1
"testbench.sv", 14: tb.unnamed$$_0: started at 30ns failed at 30ns
	Offending 'a'
[50] a=1 b=1
[70] a=1 b=1
[90] a=1 b=0
"testbench.sv", 14: tb.unnamed$$_0: started at 50ns failed at 90ns
	Offending 'b'
[110] a=1 b=1
[110] Assertion passed !
[130] a=0 b=1
"testbench.sv", 14: tb.unnamed$$_0: started at 130ns failed at 130ns
	Offending 'a'
[130] Assertion passed !
[150] a=1 b=0
"testbench.sv", 14: tb.unnamed$$_0: started at 110ns failed at 150ns
	Offending 'b'
[170] a=1 b=0
[190] a=1 b=0
"testbench.sv", 14: tb.unnamed$$_0: started at 150ns failed at 190ns
	Offending 'b'
$finish called from file "testbench.sv", line 27.
$finish at simulation time                  210
           V C S   S i m u l a t i o n   R e p o r t 
Time: 210 ns
```
![image](https://github.com/user-attachments/assets/e7a049a7-c668-43f1-85c8-f9a724c40c8e)
