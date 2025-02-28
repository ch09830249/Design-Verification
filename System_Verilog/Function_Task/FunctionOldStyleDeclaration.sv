module tb;
	initial begin
      int res, s;
      s = sum(5,9);
    	$display ("s = %0d", sum(5,9));
      $display ("sum(5,9) = %0d", sum(5,9));
      $display ("mul(3,1) = %0d", mul(3,1,res));
      $display ("res = %0d", res);
  end

  // Function has an 8-bit return value and accepts two inputs
  // and provides the result through its output port and return val
  function bit [7:0] sum;
    input int x, y;
    output sum;
		sum = x + y;
	endfunction

  // Same as above but ports are given inline
  function byte mul (input int x, y, output int res);
    res = x*y + 1;
    return x * y;
  endfunction
endmodule

/*
  s = 14
  sum(5,9) = 14
  mul(3,1) = 3
  res = 4
*/