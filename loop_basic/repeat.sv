module tb;

  	// This initial block will execute a repeat statement that will run 5 times and exit
	initial begin

        // Repeat everything within begin end 5 times and exit "repeat" block
		repeat(5) begin
			$display ("Hello World !");
		end
	end
endmodule