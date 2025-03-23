/*
  The this keyword is used to refer to "class properties", "parameters" and "methods of the current instance". 
  It can only be used within "non-static methods", "constraints" and "covergroups". 
  this is basically a pre-defined object handle that refers to the object that was used to invoke the method in which this is used.
*/

class Packet;
	bit [31:0] addr;

	function new (bit [31:0] addr);
//		addr = addr;          //  Which addr should get assigned ?

		this.addr = addr;     //  addr variable in Packet class should be         addr 就近原則
		                      //  assigned with local variable addr in new()
	endfunction
endclass