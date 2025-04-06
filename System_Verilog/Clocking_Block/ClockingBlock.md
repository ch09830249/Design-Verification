# Clocking Block
* 在介面中聲明clocking（時序區塊）和取樣的時脈訊號，可以用來實現訊號的**同步和取樣**。
* clocking 區塊基於時脈週期對訊號進行驅動或取樣的方式，使testbench不再苦惱於如何準確及時地對訊號驅動或取樣,消除了訊號競爭的問題。
```
clocking bus @(posedge clk1);
    default input #10ns output #2ns;
    input data, ready, enable;
    output negedge ack;
    input #1step addr;
endclocking
```
![image](https://github.com/user-attachments/assets/90960039-5e40-4f94-9082-7282683c0347)
* 對上述clocking描述程式碼進行說明：
  * 第一行定義 clocking 塊 bus，使用上升沿來驅動和採樣。
  * 第二行指出輸入訊號在 clk1 上升沿之前 5ns 取樣，輸出訊號在 clk1 上升沿之後 2ns 驅動（輸入為取樣，輸出為驅動）。
  * 第三行聲明輸入訊號，採用預設的輸入事件（clk1 上升沿 5ns前取樣）。
  * 第四行聲明輸出訊號，並且指明為 clk1 下降沿驅動，覆蓋了原有的 clk1 上升沿後 2ns 驅動。
  * 第五行定義了輸入訊號 addr，採用了自訂的取樣事件，clk1 上升沿後的 1 step，覆蓋了原有的 clk1 上升沿前 5ns 取樣，這裡 1 step 使得取樣發生在 clk1 上升沿的上一個時脈片取樣區域，即可以保證取樣到的資料是上一個時脈週期資料。
## clocking區塊的總結：
* clocking 區塊不只可以定義在 interface 中，也可以定義在 module 和 program 中。
* clocking 中所列舉的訊號不是自己定義的，而是 interface 或其他聲明 clocking 的模組定義的。
* clocking 在聲明完後，應該伴隨著定義預設的取樣事件，也就是 “default input/output event”，如果沒有定義，會預設使用時脈上升/下降沿前 1step 進行取樣，時脈上升/下降沿後 #0 進行驅動。
* 除了定義預設的取樣和驅動事件，定義訊號方向時同樣可以用新的取樣/驅動事件對預設事件進行覆寫。
# Example
```
module des (input req, clk, output reg gnt);
  always @ (posedge clk)  // 當 clk posedge 去檢查 req
    if (req)              // 看 req == 1 => gnt = 1, 否則 gnt = 0
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
module des (output reg[3:0] gnt);
  always #1 gnt <= $random;    // 每 1ns 指定新的隨機變數
endmodule

interface _if (input bit clk);
  logic [3:0] gnt;

  clocking cb_0 @(posedge clk);
    input #0  gnt;    // 提早 0ns drive signal
  endclocking

  clocking cb_1 @(posedge clk);
    input #1step gnt; // 提早 1step drive signal  (這裡也是 1ns)
  endclocking

  clocking cb_2 @(posedge clk);
    input #1 gnt;     // 提早 1ns drive signal
  endclocking

  clocking cb_3 @(posedge clk);
    input #2 gnt;     // 提早 2ns drive signal
  endclocking
endinterface

module tb;
  bit clk;

  always #5 clk = ~clk;  // 5ns
  initial   clk <= 0;

  _if if0 (.clk (clk));
  des d0  (.gnt (if0.gnt));

  initial begin
    fork    // 4 個 thread
      begin
        @(if0.cb_0);
        $display ("cb_0.gnt = 0x%0h", if0.cb_0.gnt);
      end
      begin
        @(if0.cb_1);
        $display ("cb_1.gnt = 0x%0h", if0.cb_1.gnt);
      end
      begin
        @(if0.cb_2);
        $display ("cb_2.gnt = 0x%0h", if0.cb_2.gnt);
      end
      begin
        @(if0.cb_3);
        $display ("cb_3.gnt = 0x%0h", if0.cb_3.gnt);
      end
    join
    #10 $finish;
  end

endmodule
```
![image](https://github.com/user-attachments/assets/4ba37170-4e68-4445-98ae-ea8e57116ffe)
![image](https://github.com/user-attachments/assets/4743827d-ba56-40a6-ad3c-12d6ff26b9a0)


/*
  ncsim> run  
  cb_3.gnt = 0x9  
  cb_2.gnt = 0x3  
  cb_1.gnt = 0x3  
  cb_0.gnt = 0xd  
  Simulation complete via $finish(1) at time 15 NS + 0  
*/

