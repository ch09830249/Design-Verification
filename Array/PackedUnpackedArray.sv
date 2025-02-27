module tb;
  bit [3:0][7:0] 	stack [2][4]; 		// 2 rows, 4 cols

	initial begin
		// Assign random values to each slot of the stack
		foreach (stack[i])
          foreach (stack[i][j]) begin
            stack[i][j] = $random;
            $display ("stack[%0d][%0d] = 0x%0h", i, j, stack[i][j]);	// 4*8 = 32 bits
			end

		// Print contents of the stack
		$display ("stack = %p", stack);

		// Print content of a given index
        $display("stack[0][0][2] = 0x%0h", stack[0][0][2]);
	end
endmodule

/*
	stack[0][0] = 0x12153524
	stack[0][1] = 0xc0895e81
	stack[0][2] = 0x8484d609
	stack[0][3] = 0xb1f05663
	stack[1][0] = 0x6b97b0d
	stack[1][1] = 0x46df998d
	stack[1][2] = 0xb2c28465
	stack[1][3] = 0x89375212
	stack = '{'{'h12153524, 'hc0895e81, 'h8484d609, 'hb1f05663}, '{'h6b97b0d, 'h46df998d, 'hb2c28465, 'h89375212}}
	stack[0][0][2] = 0x15
*/