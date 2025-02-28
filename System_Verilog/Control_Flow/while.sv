module tb;
 bit clk;

  always #10 clk = ~clk;
  
  initial begin
  	bit [3:0] counter;

    $display ("%0t: Original Counter = %0d, clk = %0d", $time, counter, clk);      // Counter = 0
  	while (counter < 10) begin
    	@(posedge clk);
    	counter++;
        $display ("%0t: After ++, Counter = %0d", $time, counter);      // Counter increments
  	end
  	$display ("%0t: Final Counter = %0d", $time, counter);      // Counter = 10
    $finish;
end
endmodule