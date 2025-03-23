
/*
    Nested object 會多 new 一個新的物件並且賦值
    Packet p1 = new;
    Packet p2 = new;
    p2.copy (p1);
*/

class Packet;
	...
   function copy (Packet p);
      this.addr = p.addr;
      this.data = p.data;
      this.hdr.id = p.hdr.id;
   endfunction
	...
endclass

module tb;
	Packet p1, p2;
	initial begin
		p1 = new (32'hface_cafe, 32'h1234_5678, 32'h1a);
		p1.display ("p1");
		
		p2 = new (1,2,3);  // give some values
		p2.copy (p1);               // 這裡做 deep copy
		p2.display ("p2");
		
		// Now let's change the addr and id in p1
		p1.addr = 32'habcd_ef12;
		p1.data = 32'h5a5a_5a5a;
		p1.hdr.id = 32'h11;
		p1.display ("p1");
		
		// Now let's print p2 - you'll see the changes made to hdr id 
		// but not addr
		p2.display ("p2");
	end
endmodule

/*
    [p1] addr=0xfacecafe data=0x12345678 id=26
    [p2] addr=0xfacecafe data=0x12345678 id=26

    [p1] addr=0xabcdef12 data=0x5a5a5a5a id=17
    [p2] addr=0xfacecafe data=0x12345678 id=26      handle 個別指向不同的 object, 所以值不同
*/