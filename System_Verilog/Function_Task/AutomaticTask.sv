/*
All items inside automatic tasks are allocated dynamically for each invocation and not shared between invocations of the same task running concurrently. 
Note that automatic task items cannot be accessed by hierarchical references.
If the task is made automatic, each invocation of the task is allocated a different space in simulation memory and behaves differently.
*/

module tb;

  initial display();
  initial display();
  initial display();
  initial display();

  // Note that the task is now automatic
  // The keyword automatic will make the task reentrant, otherwise it will be static by default.
  task automatic display();
    integer i = 0;
    i = i + 1;
    $display("i=%0d", i);
  endtask
endmodule

/*
  i=1
  i=1
  i=1
  i=1
*/