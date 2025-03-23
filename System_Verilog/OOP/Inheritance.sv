class Packet;
   int addr;

   function new (int addr1);
      this.addr = addr1;
   endfunction

	function void display ();
		$display ("[Base] addr=0x%0h", addr);
	endfunction
endclass

// A subclass called 'ExtPacket' is derived from the base class 'Packet' using
// 'extends' keyword which makes 'EthPacket' a child of the parent class 'Packet'
// The child class inherits all variables and methods from the parent class
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
	Packet      bc; 	// bc stands for BaseClass
	ExtPacket   sc; 	// sc stands for SubClass

	initial begin
		bc = new (32'hface_cafe);
		bc.display ();

        sc = new (32'hfeed_feed, 32'h1234_5678);
		sc.display ();
	end
endmodule

/*
	[Base] addr=0xfacecafe
	[Child] addr=0xfeedfeed data=0x12345678
*/