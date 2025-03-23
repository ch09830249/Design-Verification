class Packet;
	static int ctr=0;
   	bit [1:0] mode;

   function new ();
      ctr++;
   endfunction

	static function get_pkt_ctr ();
		$display ("ctr=%0d mode=%0d", ctr, mode);
	endfunction
endclass

module tb;
	Packet pkt [6];
	initial begin
		for (int i = 0; i < $size(pkt); i++) begin
			pkt[i] = new;
		end
		Packet::get_pkt_ctr(); 	// Static call using :: operator			直接透過 class name 去取
		pkt[5].get_pkt_ctr(); 	// Normal call using instance				透過物件的 handle 去取
	end
endmodule

/*
	ctr=6
	ctr=6
*/