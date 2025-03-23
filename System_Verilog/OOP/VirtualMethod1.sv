// With declaring display() as virtual
class Packet;
   int addr;

   function new (int addr);
      this.addr = addr;
   endfunction

   // Here the function is declared as "virtual"
   // so that a different definition can be given
   // in any child class
   virtual function void display ();
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
	[Child] addr=0xfeedfeed data=0x12345678
*/


// 避免在用 base class handle 時, 呼叫到 base class 的 method, 因為我們想要呼叫子 class 的 method