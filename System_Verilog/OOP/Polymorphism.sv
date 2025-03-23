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
		sc = new (32'hfeed_feed, 32'h1234_5678);

		// Assign sub-class to base-class handle
		bc = sc;

		bc.display ();
		sc.display ();
	end
endmodule

/*
	[Base] addr=0xfeedfeed						// bc.display ();
	[Child] addr=0xfeedfeed data=0x12345678s	// sc.display ();
*/


module tb;
	Packet      bc; 	// bc stands for BaseClass
	ExtPacket   sc; 	// sc stands for SubClass

	initial begin
		sc = new (32'hfeed_feed, 32'h1234_5678);
		bc = sc;

        // Print variable in sub-class that is pointed to by
        // base class handle
		$display ("data=0x%0h", bc.data);
	end
endmodule

/*
      $display ("data=0x%0h", bc.data);					父類沒有 member data
										|
	ncvlog: *E,NOTCLM (inheritance.sv,49|36): data is not a class item.
*/


module
	initial begin
		bc = new (32'hface_cafe);

        // Assign base class object to sub-class handle			不能這樣做!!
		sc = bc;

		bc.display ();
	end
endmodule

/*
	sc = bc;
				|
	ncvlog: *E,TYCMPAT (inheritance.sv,56|12): assignment operator type check failed (expecting datatype compatible with 'class $unit::ExtPacket' but found 'class $unit::Packet' instead).
*/


module
	initial begin
		bc = new (32'hface_cafe);

        // Dynamic cast base class object to sub-class type				Compile 可以過
		$cast (sc, bc); 	// 但是在 cast 會用到子類 member 導致 runtime error (父類沒有的 member)

		bc.display ();
	end
endmodule

/*
	ncsim> run
		$cast (sc, bc);
			|
	ncsim: *E,BCLCST (./inheritance.sv,57|10): Invalid cast: a value with the class datatype '$unit_0x06d772f8::Packet' cannot be assigned to a class variable with the datatype '$unit_0x06d772f8::ExtPacket'.
	[Base] addr=0xfacecafe
	ncsim: *W,RNQUIE: Simulation is complete.
*/


module
	initial begin
		ExtPacket sc2;
		bc = new (32'hface_cafe);
		sc = new (32'hfeed_feed, 32'h1234_5678);
		bc = sc;

		// Dynamic cast sub class object in base class handle to sub-class type
		$cast (sc2, bc);

		sc2.display ();
		$display ("data=0x%0h", sc2.data);
	end
endmodule

/*
	[Child] addr=0xfeedfeed data=0x12345678
	data=0x12345678
*/