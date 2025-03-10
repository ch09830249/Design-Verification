class myClass;
	rand bit [3:0] val;
	constraint  c1 { val > 3;
	                 val < 12; }

	constraint  c2  {val >= 10; }
endclass

// Note that constraints c1 and c2 limits the values to 10 and 11.

module tb;
	initial begin
		for (int i = 0; i < 10; i++) begin
			myClass cls = new ();
			cls.randomize();
			$display ("itr=%0d typ=%0d", i, cls.val);
		end
	end
endmodule

/*
  # KERNEL: itr=0 typ=11
  # KERNEL: itr=1 typ=11
  # KERNEL: itr=2 typ=11
  # KERNEL: itr=3 typ=10
  # KERNEL: itr=4 typ=11
  # KERNEL: itr=5 typ=10
  # KERNEL: itr=6 typ=10
  # KERNEL: itr=7 typ=10
  # KERNEL: itr=8 typ=10
  # KERNEL: itr=9 typ=10
*/