class myPacket;
	bit [2:0]  header;
	bit        encode;
	bit [2:0]  mode;
	bit [7:0]  data;
	bit        stop;

	function new (bit [2:0] header1 = 3'h1, bit [2:0] mode1 = 5);
		this.header = header1;
		this.encode = 0;
		this.mode   = mode1;
		this.stop   = 1;
	endfunction

	function void display ();
		$display ("Header = 0x%0h, Encode = %0b, Mode = 0x%0h, Stop = %0b",
		           this.header, this.encode, this.mode, this.stop);
	endfunction
endclass

class networkPkt extends myPacket;
	bit        parity;
	bit [1:0]  crc;

	function new ();
		super.new();			// To call the functions of base class (myPacket), use super keyword.
		this.parity = 1;
		this.crc = 3;
	endfunction

	function display();
		super.display();
		$display ("Parity = %0b, CRC = 0x%0h", this.parity, this.crc);
	endfunction
endclass

module tb_top;
	networkPkt pkt0;

	initial begin

		pkt0 = new();
		pkt0.display();
   	end
endmodule

/*
	Header = 0x1, Encode = 0, Mode = 0x5, Stop = 1
	Header = 0x1, Encode = 0, Mode = 0x5, Stop = 1
	Header = 0x1, Encode = 0, Mode = 0x5, Stop = 1
*/