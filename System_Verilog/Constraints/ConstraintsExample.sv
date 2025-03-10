class MyClass;
	rand bit [7:0] min, typ, max;

	// Valid expression
	constraint my_range { 0 < min;
	                      typ < max;
	                      typ > min;
	                      max < 128; }

	// Use of multiple operators in a single expression is not allowed
	constraint my_error { 0 < min < typ < max < 128; }

	// This will set min to 16 and randomize all others   不能用 = 
	constraint my_min {  min == 16; }

	// This will set max to a random value greater than or equal to 64
	constraint my_max {  max >= 64; }
endclass

/*
  You cannot make assignments inside a constraint block as it only contains "expressions". 
  Instead you have to use an equivalence operator == as shown for the constraint named my_min 
  in the example above where min will get a value of 16 and all other variables will be randomized. 
  This is one way of fixing a particular value to a variable even if the solver attempts to randomize it.
    EX:
      constraint my_min { min == temp.low * 9/5 + 32; }
*/

class myClass;
      rand bit [3:0] min, typ, max;
      rand bit [3:0] fixed;

      constraint my_range { 3 < min;
                            typ < max;
                            typ > min;
                            max < 14; }

      constraint c_fixed { fixed == 5; }

      function string display ();
        return $sformatf ("min=%0d typ=%0d max=%0d fixed=%d", min, typ, max, fixed);
      endfunction

endclass

module tb;
    initial begin
      for (int i = 0; i < 10; i++) begin
          myClass cls = new ();
          cls.randomize();
          $display ("itr=%0d %s", i, cls.display());
      end
    end
endmodule

/*
  # KERNEL: itr=0 min=7 typ=9 max=12 fixed= 5
  # KERNEL: itr=1 min=4 typ=9 max=12 fixed= 5
  # KERNEL: itr=2 min=7 typ=10 max=13 fixed= 5
  # KERNEL: itr=3 min=4 typ=6 max=11 fixed= 5
  # KERNEL: itr=4 min=8 typ=12 max=13 fixed= 5
  # KERNEL: itr=5 min=5 typ=6 max=13 fixed= 5
  # KERNEL: itr=6 min=6 typ=9 max=13 fixed= 5
  # KERNEL: itr=7 min=10 typ=12 max=13 fixed= 5
  # KERNEL: itr=8 min=5 typ=11 max=13 fixed= 5
  # KERNEL: itr=9 min=6 typ=9 max=11 fixed= 5
  # KERNEL: Simulation has finished. There are no more test vectors to simulate.
*/