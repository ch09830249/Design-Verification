/*
	A member declared as local is available only to the methods of the "same class", and are not accessible by child classes. 
	However, nonlocal methods that access local members can be inherited and overridden by child class.
	其實就是 C++ 的 private, nonlocal 的 method 可以被繼承和複寫
*/

class ABC;
  // By default, all variables are public and for this example,
  // let's create two variables - one public and the other "local"
  byte  	  public_var;
  local byte local_var;

  // This function simply prints these variable contents
  function void display();
    $display ("public_var=0x%0h, local_var=0x%0h", public_var, local_var);
  endfunction
endclass

module tb;
  initial begin

    // Create a new class object, and call display method
    ABC abc = new();
    abc.display();

    // Public variables can be accessed via the class handle
    $display ("public_var = 0x%0h", abc.public_var);

    // However, local variables cannot be accessed from outside
    $display ("local_var = 0x%0h", abc.local_var);
  end
endmodule

/*
	Local.sv:23: warning: Static variable initialization requires explicit lifetime in this context.     
	Local.sv:30: error: Local property local_var is not accessible in this context. (scope=tb.$unm_blk_1)
	1 error(s) during elaboration.
*/