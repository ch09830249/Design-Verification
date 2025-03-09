/*
  Syntax
    constraint  [name_of_constraint] {  [expression 1];
                                    [expression N]; }
*/

constraint  valid_addr {    addr [1:0] == 2'b0;
                            addr <= 32'hfaceface;
                            addr >= 32'hf0000000; }

constraint  fast_burst {    burst >= 3;
                            len   >= 64;
                            size  >= 128; }

// Error - valid_addr already declared
constraint valid_addr { ... }

// Runtime error - solver fails due to conflict on addr
constraint valid { addr >= 32'hfaceffff; }

// Valid because solver can find an address that satisfies all conditions
// eg :-  f200_0000 is below f400_0000 and face_face; and above f000_0000
constraint valid2 { addr <= 32'hf4000000; }

// An empty constraint - does not affect randomization
constraint c_empty;



// In-class Constraint
// Let's declare a new class called "ABC" with a single variable that
// can be randomized. We want this variable to have values between 2 and 6.
// when randomized. This is achieved by a constraint called "c_mode" (you
// can name it anything else).
class ABC;
	rand bit [3:0] mode;

	// This constraint block ensures that the randomized
	// value of "mode" meets the condition 2 < mode <= 6;
	constraint c_mode 
  { 
      mode > 2;
      mode <= 6;
  };
endclass

module tb;
	ABC abc;

	initial begin
    // Create a new object with this handle
		abc = new();

    // In a for loop, lets randomize this class handle
    // 5 times and see how the value of mode changes
    // A class can be randomized by calling its "randomize()"
		for (int i = 0; i < 5; i++) begin
			abc.randomize();
      $display ("mode = 0x%0h", abc.mode);
		end
	end
endmodule

/*
  mode = 0x6
  mode = 0x6
  mode = 0x5
  mode = 0x4
  mode = 0x5
*/


// External-class Constraint
// Let's declare a new class called "ABC" with a single variable that
// can be randomized. We want this variable to have values between 2 and 6.
// when randomized. This is achieved by a constraint called "c_mode" (you
// can name it anything else).
class ABC;
	rand bit [3:0] mode;

	constraint c_implicit; 				    // An empty constraint without "extern" is implicit
	extern constraint c_explicit; 		// An empty constraint with "extern" is explicit
endclass

// This is an external constraint because it is outside
// the class-endclass body of the class. The constraint
// is reference using ::
constraint ABC::c_implicit { mode > 2; };
constraint ABC::c_explicit { mode <= 6; };

module tb;
	ABC abc;

	initial begin
    // Create a new object with this handle
		abc = new();

    // In a for loop, lets randomize this class handle
    // 5 times and see how the value of mode changes
    // A class can be randomized by calling its "randomize()"
		for (int i = 0; i < 5; i++) begin
			abc.randomize();
      $display ("mode = 0x%0h", abc.mode);
		end
	end
endmodule

/*
  mode = 0x3
  mode = 0x5
  mode = 0x6
  mode = 0x4
  mode = 0x6
*/