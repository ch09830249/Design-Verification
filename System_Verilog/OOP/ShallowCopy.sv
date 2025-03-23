/*
  主要差別就在於 nested objects
  The nested objects are not copied entirely. Only their handles will be assigned to the new object and     只有 handle 多建立一份然後指向同樣的 object
  hence both the packets will point to the same nested object instance.

  Packet pkt, pkt2;

  pkt = new;
  pkt2 = new pkt;
*/


class Header;
	int id;
	function new (int id);
		this.id = id;
	endfunction
	
	function void showId();
		$display ("id=0x%0d", id);
	endfunction
endclass

class Packet;
	int 	addr;
	int 	data;
	Header 	hdr;
	
	function new (int addr, int data, int id);
		hdr = new (id);
		this.addr = addr;
		this.data = data;
	endfunction
	
	function void display (string name);
		$display ("[%s] addr=0x%0h data=0x%0h id=%0d", name, addr, data, hdr.id);
	endfunction
endclass

module tb;
	Packet p1, p2;
	initial begin
		// Create a new pkt object called p1
		p1 = new (32'hface_cafe, 32'h1234_5678, 26);
		p1.display ("p1");
		
		// Shallow copy p1 into p2; p2 is a new object with contents in p1
		p2 = new p1;            // 這裡做 shallow copy
		p2.display ("p2");
		
		// Now let's change the addr and id in p1
		p1.addr = 32'habcd_ef12;
		p1.data = 32'h5a5a_5a5a;
		p1.hdr.id = 17;
		p1.display ("p1");
		
		// Print p2 and see that hdr.id points to the hdr in p1, while
		// addr and data remain unchanged.
		p2.display ("p2");
	end
endmodule

/*
  [p1] addr=0xfacecafe data=0x12345678 id=26
  [p2] addr=0xfacecafe data=0x12345678 id=26

  [p1] addr=0xabcdef12 data=0x5a5a5a5a id=17
  [p2] addr=0xfacecafe data=0x12345678 id=17      因為指向同個 object, 所以兩個 handle 取出來的值相同
*/