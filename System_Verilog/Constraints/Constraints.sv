// rand
class Packet;
	rand int   		count;
	rand byte  		master [$];
	rand bit [7:0]  data [];

	...
endclass

class Packet;
	rand bit [2:0] data;
endclass

module tb;
	initial begin
		Packet pkt = new ();
		for (int i = 0 ; i < 10; i++) begin
			pkt.randomize ();
			$display ("itr=%0d data=0x%0h", i, pkt.data);
		end
	end
endmodule

/*
  # KERNEL: itr=0 data=0x7
  # KERNEL: itr=1 data=0x2
  # KERNEL: itr=2 data=0x2  // 有重複
  # KERNEL: itr=3 data=0x1
  # KERNEL: itr=4 data=0x2
  # KERNEL: itr=5 data=0x4
  # KERNEL: itr=6 data=0x0
  # KERNEL: itr=7 data=0x1
  # KERNEL: itr=8 data=0x5
  # KERNEL: itr=9 data=0x0
*/

class Packet;
	randc bit [2:0] data;
endclass

module tb;
	initial begin
		Packet pkt = new ();
		for (int i = 0 ; i < 10; i++) begin
			pkt.randomize ();
			$display ("itr=%0d data=0x%0h", i, pkt.data);
		end
	end
endmodule

/*
  # KERNEL: itr=0 data=0x6
  # KERNEL: itr=1 data=0x3
  # KERNEL: itr=2 data=0x4
  # KERNEL: itr=3 data=0x7
  # KERNEL: itr=4 data=0x0
  # KERNEL: itr=5 data=0x1
  # KERNEL: itr=6 data=0x5
  # KERNEL: itr=7 data=0x2
  # KERNEL: itr=8 data=0x5              // Start of a new sequence 直到所有值都遍歷過, 才會重複
  # KERNEL: itr=9 data=0x0
*/