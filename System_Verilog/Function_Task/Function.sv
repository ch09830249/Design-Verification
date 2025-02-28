/*
    1. The primary purpose of a function is to return a value that can be used in an expression and cannot consume simulation time.
      - A function cannot have time controlled statements like @, #, fork join, or wait
      - A function cannot start a task since tasks are allowed to consume simulation time
*/

// ANSI-C style declaration
module tb;
  	// There are two ways to call the function:
  	initial begin
      // 1. Call function and assign value to a variable, and then use variable
      int s = sum(3, 4);
      $display ("sum(3,4) = %0d", s);

      // 2. Call function and directly use value returned
      $display ("sum(5,9) = %0d", sum(5,9));

      $display ("mul(3,1) = %0d", mul(3,1));
    end

  	// This function returns value of type "byte", and accepts two
  	// arguments "x" and "y". A return variable of the same name as
  	// function is implicitly declared and hence "sum" can be directly
  	// assigned without having to declare a separate return variable
    function byte sum (int x, int y);
      sum = x + y;      // 直接用 function name 當作 return
    endfunction

  	// Instead of assigning to "mul", the computed value can be returned
  	// using "return" keyword
  	function byte mul (int x, y);
      	return x * y;
  	endfunction
endmodule

/*
  sum(3,4) = 7
  sum(5,9) = 14
  mul(3,1) = 3
*/