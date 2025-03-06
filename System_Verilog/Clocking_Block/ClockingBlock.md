# Example
```
module des (input req, clk, output reg gnt);
  always @ (posedge clk)  // 當 clk posedge 去檢查 req
    if (req) // 看 req == 1 => gnt = 1, 否則 gnt = 0
      gnt <= 1;
  	else
      gnt <= 0;
endmodule

interface _if (input bit clk);
  logic gnt;
  logic req;

  clocking cb @(posedge clk);
    input #1ns gnt;  // 這裡 gnt 會在 posedge 前 1 ns 取值接收來自 module 的輸出
    output #5  req;  // 這裡 req 會在 posedge 後 5 time units 輸出給 module (timescale 應該是 1 ns)
  endclocking
endinterface

module tb;
  bit clk;

  // Create a clock
  always #10 clk = ~clk;  // 10 ns

  // Initialize clk and req into 0
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
      bit[3:0] delay = $random;  // random 一個 delay (0~16)
      repeat (delay) @(posedge if0.clk);  // 延遲 delay 個時鐘週期
      if0.cb.req <= ~ if0.cb.req;  // 延遲完設定 req
    end
    #20 $finish;
  end
endmodule
```
**req is driven #5ns after the clock edge.**
![image](https://github.com/user-attachments/assets/f0395ddd-4f99-4d86-b20f-4a8a9c7f1c8d)
![image](https://github.com/user-attachments/assets/d935b4c3-e8ff-4f3b-90ff-6416ba698b72)


# Output skew
```
interface _if (input bit clk);
  logic gnt;
  logic req;

  clocking cb_0 @(posedge clk);
    output #0  req;  // 不延遲輸出給 module
  endclocking

  clocking cb_1 @(posedge clk);
    output #2 req;  // 延遲 2ns 輸出給 module
  endclocking

  clocking cb_2 @(posedge clk);
    output #5 req;  // 延遲 5ns 輸出給 module
  endclocking
endinterface

module tb;
  // ... part of code same as before

  // Drive stimulus
  initial begin
    for (int i = 0; i < 3; i++) begin
      repeat (2) @(if0.cb_0);  // delay 兩個 posedge
      case (i)
      	0 : if0.cb_0.req <= 1;  // Loop 0 不 delay
        1 : if0.cb_1.req <= 1;  // Loop 1 delay 2 ns
        2 : if0.cb_2.req <= 1;  // Loop 2 delay 5 ns
      endcase
      repeat (2) @ (if0.cb_0);  // 每個 Loop 再 delay 2 ns
      if0.req <= 0;  // 然後歸零 req
    end
    #20 $finish;
  end

endmodule
```
![image](https://github.com/user-attachments/assets/0354852b-7cf3-48f0-8e80-d28b60b9010e)
![image](https://github.com/user-attachments/assets/c9eb5eaa-d667-4b53-aa1b-62097b02e9e2)



# Input skew
```

```
