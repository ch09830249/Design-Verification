# Example
```
module des (input req, clk, output reg gnt);
  always @ (posedge clk)
    if (req) // 當 req == 1 => gnt = 1, 否則為
      gnt <= 1;
  	else
      gnt <= 0;
endmodule

interface _if (input bit clk);
  logic gnt;
  logic req;

  clocking cb @(posedge clk);
    input #1ns gnt;
    output #5  req;
  endclocking
endinterface

module tb;
  bit clk;

  // Create a clock and initialize input signal
  always #10 clk = ~clk;
  initial begin
    clk <= 0;
    if0.cb.req <= 0;
  end

  // Instantiate the interface
  _if if0 (.clk (clk));

  // Instantiate the design
  des d0 ( .clk (clk),
           .req (if0.req),
           .gnt (if0.gnt));

  // Drive stimulus
  initial begin
    for (int i = 0; i < 10; i++) begin
      bit[3:0] delay = $random;
      repeat (delay) @(posedge if0.clk);
      if0.cb.req <= ~ if0.cb.req;
    end
    #20 $finish;
  end
endmodule
```
**req is driven #5ns after the clock edge.**
![image](https://github.com/user-attachments/assets/f0395ddd-4f99-4d86-b20f-4a8a9c7f1c8d)

# Output skew
```
interface _if (input bit clk);
  logic gnt;
  logic req;

  clocking cb_0 @(posedge clk);
    output #0  req;
  endclocking

  clocking cb_1 @(posedge clk);
    output #2 req;
  endclocking

  clocking cb_2 @(posedge clk);
    output #5 req;
  endclocking
endinterface

module tb;
  // ... part of code same as before

  // Drive stimulus
  initial begin
    for (int i = 0; i < 3; i++) begin
      repeat (2) @(if0.cb_0);
      case (i)
      	0 : if0.cb_0.req <= 1;
        1 : if0.cb_1.req <= 1;
        2 : if0.cb_2.req <= 1;
      endcase
      repeat (2) @ (if0.cb_0);
      if0.req <= 0;
    end
    #20 $finish;
  end

endmodule
```
![image](https://github.com/user-attachments/assets/0354852b-7cf3-48f0-8e80-d28b60b9010e)


# Input skew
```

```
