// Define a simple class with a variable called "addr"
// Note that the new() function is not defined here
class Packet;
	bit [31:0] addr;
endclass

module tb;

  	// When the class object is instantiated, then the constructor is
  	// implicitly defined by the tool and called
	initial begin
		Packet pkt = new;
		$display ("addr=0x%0h", pkt.addr);
	end
endmodule

/*
  addr=0x0
*/