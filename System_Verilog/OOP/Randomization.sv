/*
	We can ensure that randomization has succeeded by using assert() function. 
	This is will avoid running simulations junk values that we may not figure until we look closer.
*/

class myPacket;

	// Declare two variables for randomization
	// mode is of type rand and hence any random value between 0 and 3 can be picked each time
	// key is of type randc and hence random values between 0 and 7 can be picked and
	// values will be repeated only after all other values have been already taken
	rand   bit [1:0]    mode;
	randc  bit [2:0]    key;		// 不重覆隨機同樣的值, 直到所以可能都被 sample 過

	// These statements are called constraints that help us to limit
	// the randomness within specified ranges
	// mode is constrained to have a value less than 3 (excluding)
	// key is constrained to have a value between 2 and 7 (excluding)
	constraint c_mode1 { mode < 3; }
	constraint c_key1  { key > 2;
                         key < 7; }

    // This is just a function to display current values of these variables
    function void display ();
       $display ("Mode : 0x%0h Key : 0x%0h", mode, key);
    endfunction
endclass

module tb_top;

	// Create a class object handle
	myPacket pkt;

	initial begin

		// Instantiate the object, and allocate memory to this variable
		pkt = new ();

		// Let's just randomize the class object 15 times and display all the
		// values randomization yielded each time
		for (int i = 0; i < 15; i++) begin

			// By using assert(), we are ensuring that randomization is successful.
			assert (pkt.randomize ());	// 若是 false 會停止 simulation
			pkt.display ();
		end
	end
endmodule

/*
	Mode : 0x0 Key : 0x3
	Mode : 0x0 Key : 0x5
	Mode : 0x0 Key : 0x4
	Mode : 0x0 Key : 0x6
	Mode : 0x2 Key : 0x4
	Mode : 0x1 Key : 0x6
	Mode : 0x2 Key : 0x5
	Mode : 0x0 Key : 0x3
	Mode : 0x1 Key : 0x3
	Mode : 0x2 Key : 0x6
	Mode : 0x0 Key : 0x4
	Mode : 0x0 Key : 0x5
	Mode : 0x0 Key : 0x5
	Mode : 0x1 Key : 0x6
	Mode : 0x0 Key : 0x3
*/




class myPacket;
	rand   bit [7:0] mode;
	randc  bit [7:0] key;
	int  low, high;

	constraint c_simple {  mode > 2;
	                       key == 3; }

// This won't work, because it contradicts c_simple - Run-time error  // 與 c_simple 矛盾 => runtime error
//	constraint c_key    {  key < 2; }

// This won't work either, because of wrong syntax - you can't specify it this way
//  constraint c_signs  {  0 < key < 4; }		// 要改成 key < 4; key > 0;

    constraint c_range  { key inside {[low:high]};
    					mode inside {[21:50]};
    					mode inside {23, 24, 51}; }

// Choose any value other than 2,3,4,5
    constraint c_invert { !(key inside {[2:5]}); }

// Choose 10 or 22 ; with equal probability even if 10 and 20 appeared multiple times
    constraint c_weight { mode inside {10, 10, 10, 22, 22};

// 4 has 50/130 chance, 43 has 10/130 chance, any value between 45:90 has 70/130 chance
    constraint c_key_dist  { key  dist {4:=50, 43:=10, [45:90]:=70 };

// 4 has 10/100 chance, 43 has 30/100 chance, any value between 45:47 has 20/100 chance
    constraint c_mode_dist { mode dist {4:/10, 43:/30, [45:47]:/60 };

    function void pre_randomize ();
       this.low = 1;
       this.high = 2;
    endfunction
endclass