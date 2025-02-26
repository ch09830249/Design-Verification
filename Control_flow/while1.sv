module tb;
	initial begin
		int cnt = 0;
		while (cnt < 5) begin
			$display("cnt = %0d", cnt);
			cnt++;
		end
	end
endmodule