/*
  The method returns 1 if randomization was successful, and 0 if it failed. 
  It can fail due to a variety of reasons like 
    1. conflicting constraints, 
    2. solver could not come up with a value that meets all constraints and such. 
  Class objects are not randomized automatically, and hence 
  we should always call the randomize() method to do randomization.
*/
class Beverage;
  rand bit [7:0]	beer_id;
  constraint c_beer_id { beer_id >= 10;
                        beer_id <= 50; };

endclass

module tb;
   Beverage b;

    initial begin
      b = new ();
      $display ("Initial beerId = %0d", b.beer_id);
      if (b.randomize ())
      	$display ("Randomization successful !");
      $display ("After randomization beerId = %0d", b.beer_id);
    end
endmodule

/*
  # KERNEL: Initial beerId = 0
  # KERNEL: Randomization successful !
  # KERNEL: After randomization beerId = 25
*/


// pre_randomize()
// This function is defined within the same class whose object will be randomized and called before randomization().
class Beverage;
  rand bit [7:0]	beer_id;

  constraint c_beer_id { beer_id >= 10;
                        beer_id <= 50; };

  function void pre_randomize ();
  	$display ("This will be called just before randomization");
  endfunction
endclass

/*
  # KERNEL: Initial beerId = 0
  # KERNEL: This will be called just before randomization
  # KERNEL: Randomization successful !
  # KERNEL: After randomization beerId = 25
*/


// post_randomize()
// This function is also defined within the same class whose object will be randomized and called after randomization().
class Beverage;
  rand bit [7:0]	beer_id;

  constraint c_beer_id { beer_id >= 10;
                        beer_id <= 50; };

  function void pre_randomize ();
  	$display ("This will be called just before randomization");
  endfunction

  function void post_randomize ();
  	$display ("This will be called just after randomization");
  endfunction

endclass

/*
  # KERNEL: Initial beerId = 0
  # KERNEL: This will be called just before randomization
  # KERNEL: This will be called just after randomization
  # KERNEL: Randomization successful !
  # KERNEL: After randomization beerId = 25
*/

/*
  PS:
    1. If randomize() fails, then post_randomize() is not called 
    2. randomize() method is built-in and cannot be overriden
    3. If randomization fails, then the variables retain their original values and are not modified
    4. pre_randomize() and post_randomize() are not virtual
*/