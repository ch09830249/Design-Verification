module tb;
 bit clk;

  always #10 clk = ~clk;
  initial begin
  	bit [3:0] counter;

    $display ("%0t: Counter = %0d", $time, counter);      // Counter = 0
		do begin
      @ (posedge clk);
      counter ++;
      $display ("%0t: Counter = %0d", $time, counter);      // Counter increments
    end while (counter < 5);
    $display ("%0t: Final Counter = %0d", $time, counter);      // Counter = 14
    $finish;
  end
endmodule