/*
	The super keyword is used from "within a sub-class" to refer to "properties and methods of the base class". 
	It is mandatory to use the super keyword to access properties and methods if they have been overridden by the sub-class. 
	若是沒用 super 則使用子類的 method 或 property
*/

class Packet;
	int addr;
	function void display ();
		$display ("[Base] addr=0x%0h", addr);
	endfunction
endclass

class extPacket;                       // "extends" keyword missing -> not a child class
	function new ();
		super.new();
	endfunction
endclass

module tb;
	Packet p;
  	extPacket ep;

  	initial begin
      ep = new();
      p = new();
      p.display();
    end
endmodule

/*
	Super.sv:16: error: Class extPacket has no parent class for super.new constructor chaining.
	1 error(s) during elaboration.
*/