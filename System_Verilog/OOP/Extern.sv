// Using extern qualifier in method declaration indicates that the implementation is done "outside the body of this class".

class ABC;

  // Let this function be declared here and defined later
  // by "extern" qualifier
  extern function void display();

endclass

// Outside the class body, we have the implementation of the
// function declared as "extern"
function void ABC::display();

   $display ("Hello world");

endfunction

module tb;

  // Lets simply create a class object and call the display method
  initial begin
    ABC abc = new();
    abc.display();
  end
endmodule

/*
	Hello world
*/