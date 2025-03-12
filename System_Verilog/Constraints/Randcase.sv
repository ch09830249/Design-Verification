/*
    The keyword randcase introduces a case statement that randomly selects one of its branches. 
    The case item expressions are positive integer values that represent the weights associated with each item.     數字代表該 item 的權重
    Probability of selecting an item is derived by the division of that item's weight divided by the sum of all weights.
*/

module tb;
	initial begin
      for (int i = 0; i < 10; i++)
      	randcase
        	1 	: 	$display ("Wt 1");
      		5 	: 	$display ("Wt 5");
      		3 	: 	$display ("Wt 3");
      	endcase
    end
endmodule

/*
    Wt 5
    Wt 5
    Wt 3
    Wt 5
    Wt 1
    Wt 3
    Wt 5
    Wt 3
    Wt 3
    Wt 5
*/

// PS: If a branch specifies a zero weight, then that branch is not taken.

module tb;
	initial begin
      for (int i = 0; i < 10; i++)
      	randcase
        	0 	: 	$display ("Wt 1");  // 權重為 0, 將不會再被取用
      		5 	: 	$display ("Wt 5");
      		3 	: 	$display ("Wt 3");
      	endcase
    end
endmodule

/*
    Wt 5
    Wt 5
    Wt 3
    Wt 5
    Wt 5
    Wt 3
    Wt 5
    Wt 3
    Wt 3
    Wt 5
*/

// PS: 若全 0, 可能會產生 run-time warning
module tb;
	initial begin
      for (int i = 0; i < 10; i++)
      	randcase
        	0 	: 	$display ("Wt 1");
      		0 	: 	$display ("Wt 5");
      		0 	: 	$display ("Wt 3");
      	endcase
    end
endmodule

/*
    ncsim: *W,RANDNOB: The sum of the weight expressions in the randcase statement is 0.
    No randcase branch was taken.
                File: ./testbench.sv, line = 4, pos = 14
            Scope: tb.unmblk1
                Time: 0 FS + 0

    ncsim: *W,RANDNOB: The sum of the weight expressions in the randcase statement is 0.
    No randcase branch was taken.
                File: ./testbench.sv, line = 4, pos = 14
            Scope: tb.unmblk1
                Time: 0 FS + 0

    ncsim: *W,RANDNOB: The sum of the weight expressions in the randcase statement is 0.
    No randcase branch was taken.
                File: ./testbench.sv, line = 4, pos = 14
            Scope: tb.unmblk1
                Time: 0 FS + 0
                
                ...
*/