/*
  The example above declares a class called Pkt with a constraint on its address field. 
  Note that both its properties are prefixed with the rand keyword which tells the solver that these variables should be randomized when asked to. 
  The constraint is called addr_limit and specifies that the solver can allot any random value for the address that is below or equal to 8'h8. 
  Since the 8-bit variable addr is of type bit, it can have any value from 0 to 255, but with the constraint valid values will be limited to 11.
*/

class Pkt;
	rand bit [7:0] addr;
	rand bit [7:0] data;

	constraint addr_limit { addr <= 8'hB; }
endclass