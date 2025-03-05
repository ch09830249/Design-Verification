/*
  1. An up-down counter in Verilog
  2. This module accepts a parameter to decide the width of the counter => WIDTH 絕對 counter 幾個 bits
  3. It also accepts an input load value load that is loaded into the counter only when load_en is 1. => load_en == 1, 將值從 load 載入 counter
  4.   The counter starts counting down when the input down is 1 and  => down 的時候做 --, 否則做 ++
        otherwise it counts upwards. 
  5. The rollover output indicates when the counter either transitions from a max_value to 0 or a 0 to max_value.
*/

// This module accepts an interface object as the port list
module counter_ud  #(parameter WIDTH = 4) (cnt_if _if);   // 這裡 DUT 的輸入從各個 signals 改成接收 interface
  always @ (posedge _if.clk or negedge _if.rstn) begin
    if (!_if.rstn)      // module 取信號也是透過 interface 取信號
   		_if.count <= 0;
    else
      if (_if.load_en)
        _if.count <= _if.load;
      else begin
        if (_if.down)
        	_if.count <= _if.count - 1;
      	else
        	_if.count <= _if.count + 1;
      end
  end

  assign _if.rollover = &_if.count;
endmodule

/*
  這裡定義一個 interface
*/
interface cnt_if #(parameter WIDTH = 4) (input bit clk);
  logic 			rstn;
  logic 			load_en;
  logic [WIDTH-1:0] load;
  logic [WIDTH-1:0] count;
  logic 			down;
  logic 			rollover;
endinterface

module tb;
  reg clk;

  // TB Clock Generator used to provide the design
  // with a clock -> here half_period = 10ns => 50 MHz
  always #10 clk = ~clk;

  cnt_if 	  cnt_if0 (clk);  // 例化一個 interface

  // Note that here we just have to pass the interface handle
  // to the design instead of connecting each individual signal
  counter_ud  c0 (cnt_if0);   // 直接改傳入 interface 的 instance

  initial begin
    bit load_en, down;
    bit [3:0] load;

    $monitor("[%0t] down=%0b load_en=%0b load=0x%0h count=0x%0h rollover=%0b",
    	$time, cnt_if0.down, cnt_if0.load_en, cnt_if0.load, cnt_if0.count, cnt_if0.rollover);   // 只要 interface 中的訊號出現變化, 就印出值

    // Initialize testbench variables
    clk <= 0;
    cnt_if0.rstn <= 0;
    cnt_if0.load_en <= 0;
    cnt_if0.load <= 0;
    cnt_if0.down <= 0;

    // Drive design out of reset after 5 clocks
    repeat (5) @(posedge clk);
    cnt_if0.rstn <= 1;

    // Drive stimulus -> repeat 5 times
    for (int i = 0; i < 5; i++) begin

      // Drive inputs after some random delay
      int delay = $urandom_range (1,30);
      #(delay);

      // Randomize input values to be driven
      std::randomize(load, load_en, down);

      // Assign tb values to interface signals
      cnt_if0.load <= load;
      cnt_if0.load_en <= load_en;
      cnt_if0.down <= down;
    end

    // Wait for 5 clocks and finish simulation
    repeat(5) @ (posedge clk);
    $finish;
  end
endmodule

/*
  [0] down=0 load_en=0 load=0x0 count=0x0 rollover=0
  [96] down=1 load_en=1 load=0x1 count=0x0 rollover=0
  [102] down=0 load_en=0 load=0x9 count=0x0 rollover=0
  [108] down=1 load_en=1 load=0x1 count=0x0 rollover=0
  [110] down=1 load_en=1 load=0x1 count=0x1 rollover=0
  [114] down=1 load_en=0 load=0xc count=0x1 rollover=0
  [120] down=1 load_en=0 load=0x7 count=0x1 rollover=0
  [130] down=1 load_en=0 load=0x7 count=0x0 rollover=0
  [150] down=1 load_en=0 load=0x7 count=0xf rollover=1
  [170] down=1 load_en=0 load=0x7 count=0xe rollover=0
  [190] down=1 load_en=0 load=0x7 count=0xd rollover=0
*/