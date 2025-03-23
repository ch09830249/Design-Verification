// Define a base class and let the variable be "local" to this class
class ABC;
  local byte local_var;
endclass

// Define another class that extends ABC and have a function that tries
// to access the local variable in ABC
class DEF extends ABC;
  function void show();
    $display ("local_var = 0x%0h", local_var);
  endfunction
endclass

module tb;
  initial begin

    // Create a new object of the child class, and call the show method
    // This will give a compile time error because child classes cannot access
    // base class "local" variables and methods
    DEF def = new();
    def.show();

  end
endmodule

/*
 $display ("local_var = 0x%0h", local_var);
                                           |
ncvlog: *E,CLSNLO (testbench.sv,10|43): Access to local member 'local_var' in class 'ABC' is not allowed here.
irun: *E,VLGERR: An error occurred during parsing.  Review the log file for errors with the code *E and fix those identified problems to proceed.  Exiting with code (status 1).
*/