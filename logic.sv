module tb;
	reg [3:0] r1, r2;
	wire [3:0] w1, w2;
	logic [3:0] v1, v2;

	assign w1 = 4'b0011;
	assign w2 = 4'b0111;

	initial begin
		r1 = 4'b1111;
		r2 = 4'b0110;
	end

	initial begin
		#0;
		$display("%0t: v1 = b%b, v2 = b%b", $time, v1, v2);
		$display("%0t: w1 = b%b, w2 = b%b", $time,  w1, w2);
		$display("%0t: r1 = b%b, r2 = b%b", $time,  r1, r2);
		#1;
		v1 = w1;
		v2 = w2;
		$display("%0t: v1 = b%b, v2 = b%b", $time,  v1, v2);
		#1;
		v1 = r1;
		v2 = r2;
		$display("%0t: v1 = b%b, v2 = b%b", $time, v1, v2);
	end
endmodule