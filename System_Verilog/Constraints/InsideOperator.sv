/*
  <variable> inside {<values or range>}

  // Inverted "inside"
  !(<variable> inside {<values or range>})


  m_var inside {4, 7, 9} 		// Check if m_var is either 4,7 or 9
  m_var inside {[10:100]} 	// Check if m_var is between 10 and 100 inclusive
*/


constraint my_range { typ > 32;
                      typ < 256; }

// typ >= 32 and typ <= 256
constraint new_range { typ inside {[32:256]}; }

// Choose from the following values
constraint spec_range { type inside {32, 64, 128}; }

/* This will produce a random value from 0 to 31 since typ is an 8-bit variable 
and the upper limit already covers the maximum value it can hold.
Note that repeated randomization gave all values except the ones that fall within the range 3 through 6.*/
rand bit [2:0] typ;
constraint inv_range { ! (typ inside {[3:6]}); }  // 0~31 中隨機除了 3~6 的值

/*
  # KERNEL: itr=0 typ=7
  # KERNEL: itr=1 typ=0
  # KERNEL: itr=2 typ=7
  # KERNEL: itr=3 typ=0
  # KERNEL: itr=4 typ=0
  # KERNEL: itr=5 typ=0
  # KERNEL: itr=6 typ=7
  # KERNEL: itr=7 typ=1
  # KERNEL: itr=8 typ=1
  # KERNEL: itr=9 typ=7
*/


// if-else
module tb;
	bit [3:0] 	m_data;
	bit 		    flag;
	initial begin
		for (int i = 0; i < 10; i++) begin
			m_data = $random;

			// Used in a ternary operator
			flag = m_data inside {[4:9]} ? 1 : 0;

			// Used with "if-else" operators
			if (m_data inside {[4:9]})
				$display ("m_data=%0d INSIDE [4:9], flag=%0d", m_data, flag);
			else
				$display ("m_data=%0d outside [4:9], flag=%0d", m_data, flag);
		end
	end
endmodule

/*
  m_data=4 INSIDE [4:9], flag=1
  m_data=1 outside [4:9], flag=0
  m_data=9 INSIDE [4:9], flag=1
  m_data=3 outside [4:9], flag=0
  m_data=13 outside [4:9], flag=0
  m_data=13 outside [4:9], flag=0
  m_data=5 INSIDE [4:9], flag=1
  m_data=2 outside [4:9], flag=0
  m_data=1 outside [4:9], flag=0
  m_data=13 outside [4:9], flag=0
*/


// Used in Constraints
class ABC;
	rand bit [3:0] 	m_var;
	// Constrain m_var to be either 3,4,5,6 or 7
	constraint c_var { m_var inside {[3:7]}; }
endclass

module tb;
	initial begin
		ABC abc = new();
		repeat (5) begin
			abc.randomize();
			$display("abc.m_var = %0d", abc.m_var);
		end
	end
endmodule

/*
  abc.m_var = 7
  abc.m_var = 6
  abc.m_var = 6
  abc.m_var = 3
  abc.m_var = 4
*/


// Inverted inside
class ABC;
	rand bit [3:0] 	m_var;
	// Inverted inside: Constrain m_var to be outside 3 to 7
	constraint c_var { !(m_var inside {[3:7]}); }
endclass

module tb;
	initial begin
		ABC abc = new();
		repeat (5) begin
			abc.randomize();
			$display("abc.m_var = %0d", abc.m_var);
		end
	end
endmodule

/*
  abc.m_var = 1
  abc.m_var = 12
  abc.m_var = 0
  abc.m_var = 14
  abc.m_var = 10
*/

// Particle Example
/*
  Say we have a memory located between the address range 0x4000 and 0x5FFF, 
  which is partitioned into two. The first part is used to store instructions 
  and the second part to store data. Say we want to randomize the address for data 
  such that the address falls within the data part of memory, we can easily use the inside operator.
*/
class Data;
	rand bit [15:0] 	m_addr;
	constraint c_addr 	{ m_addr inside {[16'h4000:16'h4fff]}; }
endclass

module tb;
	initial begin
		Data data = new();
		repeat (5) begin
			data.randomize();
			$display ("addr = 0x%0h", data.m_addr);
		end
	end
endmodule

/*
  addr = 0x48ef
  addr = 0x463f
  addr = 0x4612
  addr = 0x4249
  addr = 0x4cee
*/