/*
  Non-blocking assignment allows assignments to be scheduled without blocking the execution of following statements and is specified by a <= symbol.  一起 assign, 沒有先後
  It's interesting to note that the same symbol is used as a relational operator in expressions, and as an assignment operator in the context of a non-blocking assignment. 
  If we take the first example from above, replace all = symobls with a non-blocking assignment operator <=, we'll see some difference in the output.
*/
/*
  See that all the $display statements printed 'h'x. The reason for this behavior lies in the way non-blocking assignments are executed. 
  The RHS of every non-blocking statement of a particular time-step is captured, and moves onto the next statement. 
  The captured RHS value is assigned to the LHS variable only at the end of the time-step.
*/
module tb;
  reg [7:0] a, b, c, d, e;

  initial begin
    a <= 8'hDA;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
    b <= 8'hF1;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
    c <= 8'h30;
    $display ("[%0t] a=0x%0h b=0x%0h c=0x%0h", $time, a, b, c);
  end

  initial begin
    d <= 8'hAA;
    $display ("[%0t] d=0x%0h e=0x%0h", $time, d, e);
 	  e <= 8'h55;
    $display ("[%0t] d=0x%0h e=0x%0h", $time, d, e);
  end
endmodule

/*
  [0] a=0xxx b=0xxx c=0xxx
  [0] a=0xxx b=0xxx c=0xxx
  [0] a=0xxx b=0xxx c=0xxx
  [0] d=0xxx e=0xxx
  [0] d=0xxx e=0xxx
*/

/*
|__ Spawn Block1: initial
|      |___ Time #0ns : a <= 8'DA, is non-blocking so note value of RHS (8'hDA) and execute next step
|      |___ Time #0ns : $display() is blocking, so execute this statement: But a hasn't received new values so a=8'hx
|      |___ Time #0ns : b <= 8'F1, is non-blocking so note value of RHS (8'hF1) and execute next step
|      |___ Time #0ns : $display() is blocking, so execute this statement. But b hasn't received new values so b=8'hx
|      |___ Time #0ns : c <= 8'30, is non-blocking so note value of RHS (8'h30) and execute next step
|      |___ Time #0ns : $display() is blocking, so execute this statement. But c hasn't received new values so c=8'hx
|      |___ End of time-step and initial block, assign captured values into variables a, b, c   => timestep 0ns 的最後 assign a, b, c value
|
|__ Spawn Block2: initial
|      |___ Time #0ns : d <= 8'AA, is non-blocking so note value of RHS (8'hAA) and execute next step
|      |___ Time #0ns : $display() is blocking, so execute this statement: But d hasn't received new values so d=8'hx
|      |___ Time #0ns : e <= 8'55, is non-blocking so note value of RHS (8'h55) and execute next step
|      |___ Time #0ns : $display() is blocking, so execute this statement. But e hasn't received new values so e=8'hx
|      |___ End of time-step and initial block, assign captured values into variables d and e   => timestep 0ns 的最後 assign d, e value
|
|__ End of simulation at #0ns
*/