// Define a simple class and initialize the class member "data" in new() function
class baseClass;
  bit [15:0] data;

  function new ();
    data = 16'hface;
  endfunction
endclass

// Define a child class extended from the above class with more members
// The constructor new() function accepts a value as argument, and by default is 2
class subClass extends baseClass;
  bit [3:0] id;
  bit [2:0] mode = 3;

  function new (int val = 2);
    // The new() function in child class calls the new function in
    // the base class using the "super" keyword
    super.new ();	// 先呼叫父類的 new

    // Assign the value obtained through the argument to the class member
    id = val;
  endfunction
endclass

module tb;
  initial begin
    // Create two handles for the child class
    subClass  sc1, sc2;

    // Instantiate the child class and display member variable values
    sc1 = new ();
    $display ("data=0x%0h id=%0d mode=%0d", sc1.data, sc1.id, sc1.mode);

    // Pass a value as argument to the new function in this case and print
    sc2 = new (4);
    $display ("data=0x%0h id=%0d mode=%0d", sc2.data, sc2.id, sc2.mode);
  end
endmodule

/*
	data=0xface id=2 mode=3
	data=0xface id=4 mode=3
*/