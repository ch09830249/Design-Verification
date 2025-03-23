/*
	In Inheritance, we saw that methods invoked by a base class handle which points to a child class instance would eventually 
	end up executing the base class method instead of the one in child class. If that function in the base class was declared 
	as virtual, only then the child class method will be executed.
*/

// Without declaring display() as virtual
class Packet;
   int addr;

   function new (int addr);
      this.addr = addr;
   endfunction

   // This is a normal function definition which
   // starts with the keyword "function"
   function void display ();
		$display ("[Base] addr=0x%0h", addr);
   endfunction
endclass

class ExtPacket extends Packet;

	// This is a new variable only available in child class
	int data;

	function new (int addr1, data1);
		super.new (addr1); 	// Calls 'new' method of parent class
		this.data = data1;
	endfunction

	function void display ();
		$display ("[Child] addr=0x%0h data=0x%0h", addr, data);
	endfunction
endclass

module tb;
   Packet bc;
   ExtPacket sc;

	initial begin
        sc = new (32'hfeed_feed, 32'h1234_5678);

        bc = sc;
		bc.display ();
	end
endmodule

/*
	[Base] addr=0xfeedfeed
*/