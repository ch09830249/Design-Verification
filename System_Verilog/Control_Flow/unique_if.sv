/*
unique-if/unique0-if evaluates conditions in any order and does the following :  => 若以下任一條件滿足, report an error

    report an error when none of the if conditions match unless there is an explicit else.  => 沒有任何一個 condition 滿足, 除非有 else
    report an erorr when there is more than 1 match found in the if else conditions   => 超過 1 個 condition 滿足
*/

module tb;
	int x = 4;

  initial begin
    // This if else if construct is declared to be "unique"
    // Error is not reported here because there is a "else"
    // clause in the end which will be triggered when none of
    // the conditions match
    unique if (x == 3)
      $display ("x is %0d", x);
    else if (x == 5)
      $display ("x is %0d", x);
    else
      $display ("x is neither 3 nor 5");  // 因為有 else, 所以不會 report an error

    // When none of the conditions become true and there
    // is no "else" clause, then an error is reported
    unique if (x == 3)
      $display ("x is %0d", x);
    else if (x == 5)
        $display ("x is %0d", x);
  end
endmodule

/*
  x is neither 3 nor 5
  ncsim: *W,NOCOND: Unique if violation:  Every if clause was false.
              File: ./testbench.sv, line = 18, pos = 13
            Scope: tb
              Time: 0 FS + 1
*/

module tb;
	int x = 4;

  	initial begin
      // This if else if construct is declared to be "unique"
      // When multiple if blocks match, then error is reported
      unique if (x == 4)
        $display ("1. x is %0d", x);  // 滿足
      else if (x == 4)
        $display ("2. x is %0d", x);  // 滿足
      else
        $display ("x is not 4");
  	end
endmodule

/*
  1. x is 4
  ncsim: *W,MCONDE: Unique if violation:  Multiple true if clauses at {line=8:pos=15 and line=10:pos=13}.
              File: ./testbench.sv, line = 8, pos = 15
            Scope: tb
              Time: 0 FS + 1
*/