/*
  first()	  function enum first();	                  Returns the value of the first member of the enumeration
  last()	  function enum last();	                    Returns the value of the last member of the enumeration
  next()	  function enum next (int unsigned N = 1);	Returns the Nth next enumeration value starting from the current value of the given variable
  prev()	  function enum prev (int unsigned N = 1);	Returns the Nth previous enumeration value starting from the current value of the given variable
  num()	    function int num();	                      Returns the number of elements in the given enumeration
  name()	  function string name();	                  Returns the string representation of the given enumeration value
*/

// GREEN = 0, YELLOW = 1, RED = 2, BLUE = 3
typedef enum {GREEN, YELLOW, RED, BLUE} colors;

module tb;
	initial begin
      colors color;

      // Assign current value of color to YELLOW
      color = YELLOW;

      $display ("color.first() = %0d", color.first());  // First value is GREEN = 0
      $display ("color.last()  = %0d", color.last());	// Last value is BLUE = 3
      $display ("color.next()  = %0d", color.next()); 	// Next value is RED = 2
      $display ("color.prev()  = %0d", color.prev()); 	// Previous value is GREEN = 0
      $display ("color.num()   = %0d", color.num()); 	// Total number of enum = 4
      $display ("color.name()  = %s" , color.name()); 	// Name of the current enum

      color = GREEN;
      $display ("color.name()  = %s" , color.name()); 	// Name of the current enum
      $display ("color.prev()  = %0d", color.prev()); 	// Previous value is BLUE = 3

      color = BLUE;
      $display ("color.name()  = %s" , color.name()); 	// Name of the current enum
      $display ("color.next()  = %0d", color.next()); 	// Next value is GREEN = 0
    end
endmodule

/*
  color.first() = 0
  color.last()  = 3
  color.next()  = 2
  color.prev()  = 0
  color.num()   = 4
  color.name()  = YELLOW
  color.name()  = GREEN
  color.prev()  = 3
  color.name()  = BLUE
  color.next()  = 0
*/