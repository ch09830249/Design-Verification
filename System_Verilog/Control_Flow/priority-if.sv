/*
priority-if evaluates all conditions in sequential order and a violation is reported when:    priority 循序運算 expression/unique 則是平行運算 expression

  None of the conditions are true or if there's no else clause to the final if construct    只要沒有條件滿足或是最後沒有 else block, 就會 report an error
*/

module tb;
	int x = 4;

  	initial begin
      // This if else if construct is declared to be "unique"
      // Error is not reported here because there is a "else"
      // clause in the end which will be triggered when none of
      // the conditions match
    	priority if (x == 3)
      		$display ("x is %0d", x);
    	else if (x == 5)
      		$display ("x is %0d", x);
      else
      		$display ("x is neither 3 nor 5");

      // When none of the conditions become true and there
      // is no "else" clause, then an error is reported
    	priority if (x == 3)
      		$display ("x is %0d", x);
    	else if (x == 5)
      		$display ("x is %0d", x);
  	end
endmodule

/*
  x is neither 3 nor 5
  ncsim: *W,NOCOND: Priority if violation:  Every if clause was false.
              File: ./testbench.sv, line = 18, pos = 15
            Scope: tb
              Time: 0 FS + 1
*/

module tb;
	int x = 4;

  	initial begin
      // Exits if-else block once the first match is found
      priority if (x == 4)    // 就算多個 condition 滿足, 也只會執行第一個滿足就跳出 if-else, 不會 report an error 
                              // (與 unique 不同, priority 是循序執行, 所以不會意識到後面還有條件滿足 unique 因為是平行運算, 所以會 report an error)
        $display ("x is %0d", x);
      else if (x != 5)
        $display ("x is %0d", x);
  	end
endmodule

/*
  x is 4
*/