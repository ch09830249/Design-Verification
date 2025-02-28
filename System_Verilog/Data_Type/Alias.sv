/*
	An alias is a named reference to a variable, signal, or instance.
*/

module tb;
	logic [7:0] data;
	alias mydata = data; // alias "mydata" for signal "data"

	initial begin
		mydata = 8'hFF; // assign the value to "data" using the alias "mydata"
		$display("mydata=%0h, data=%0h", mydata, data);
	end
endmodule