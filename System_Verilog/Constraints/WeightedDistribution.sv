/*
  一般來說所以數值隨機產生的機率都是一樣的, 但這裡可以加上權重
  The dist operator allows you to create weighted distributions so that some values are chosen more often than others. 
  The := operator specifies that the weight is the same for every specified value in the range while 
  the :/ operator specifies that the weight is to be equally divided between all the values.
*/


// := operator
class myClass;
	rand bit [2:0] typ;
	constraint dist1 	{  typ dist { 0:=20, [1:5]:=50, 6:=40, 7:=10}; }    // [1:5]:=50 => 1~5 每個都 50  total=20+5*50+40+10=320
endclass

module tb;
	initial begin
		for (int i = 0; i < 10; i++) begin
			myClass cls = new ();
			cls.randomize();
			$display ("itr=%0d typ=%0d", i, cls.typ);
		end
	end
endmodule

/*
  # KERNEL: itr=0 typ=5
  # KERNEL: itr=1 typ=1
  # KERNEL: itr=2 typ=6
  # KERNEL: itr=3 typ=3
  # KERNEL: itr=4 typ=2
  # KERNEL: itr=5 typ=3
  # KERNEL: itr=6 typ=0
  # KERNEL: itr=7 typ=5
  # KERNEL: itr=8 typ=1
  # KERNEL: itr=9 typ=4
*/

// :/ operator
class myClass;
	rand bit [2:0] typ;
	constraint dist2 	{  typ dist { 0:/20, [1:5]:/50, 6:/40, 7:/10}; }  // [1:5]:/50 => 1~5 平分 50 的權重, 所以每個佔 10 total=20+50+40+10=100
endclass

module tb;
	initial begin
		for (int i = 0; i < 10; i++) begin
			myClass cls = new ();
			cls.randomize();
			$display ("itr=%0d typ=%0d", i, cls.typ);
		end
	end
endmodule

/*
  # KERNEL: itr=0 typ=5
  # KERNEL: itr=1 typ=6
  # KERNEL: itr=2 typ=4
  # KERNEL: itr=3 typ=6
  # KERNEL: itr=4 typ=6
  # KERNEL: itr=5 typ=4
  # KERNEL: itr=6 typ=2
  # KERNEL: itr=7 typ=3
  # KERNEL: itr=8 typ=4
  # KERNEL: itr=9 typ=6
*/