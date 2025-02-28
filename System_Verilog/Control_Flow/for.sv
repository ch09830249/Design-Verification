module tb;
 bit clk;

  always #10 clk = ~clk;
  initial begin
  	bit [3:0] counter;

    $display ("%0t: Counter = %0d", $time, counter);      // Counter = 0
  	for (counter = 2; counter < 14; counter = counter + 2) begin
    	@(posedge clk);
    	$display ("%0t: Counter = %0d", $time, counter);      // Counter increments
  	end
    $display ("%0t: Final Counter = %0d", $time, counter);      // Counter = 14
    $finish;
  end
endmodule