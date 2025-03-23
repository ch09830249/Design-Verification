class Packet;
	static int ctr=0;

	function new ();
		ctr++;
	endfunction

	static function get_pkt_ctr ();			// Static function 不能取用非 static member, 因為物件可能還沒有被創建
		$display ("ctr=%0d", ctr);
	endfunction

endclass

/*
$display ("ctr=%0d mode=%0d", ctr, mode);
                                                      |
ncvlog: *E,CLSNSU (static-function.sv,10|40): A static class method cannot access non static class members.
*/