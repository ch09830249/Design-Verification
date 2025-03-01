module tb;
	parameter   WIDTH = 8;
	reg [WIDTH-1:0]   m_var;
	reg [7:0]  m_var1;
	reg [15:0] m_var2;
	real  pi;        // Declared to be of type real
  	real  freq;
	bit   [3:0] var_b;      // Declare a 4-bit variable of type "bit"
  	logic [3:0] x_val;     // Declare a 4-bit variable of type "logic"
	bit       var_a1;       // Declare a 1 bit variable of type "bit"
	bit [3:0] var_b1;       // Declare a 4 bit variable of type "bit"
	logic [3:0] x_val1;     // Declare a 4 bit variable of type "logic"
	byte           m_var_s;      // By default signed, and can represent positive and negative numbers

	initial begin
		begin
			m_var = 'h0;     // Fills all bits of m_var with 0
			$display("m_var=0x%0h", m_var);
			m_var = 'hZ;     // Fills all bits of m_var with Z
			$display("m_var=0x%0h", m_var);
			m_var = 'hX;     // Fills all bits of m_var with X
			$display("m_var=0x%0h", m_var);
			m_var = 'h1;     // Only LSB is 1 making the value of m_var = 8'b0000_0001
			$display("m_var=0x%0h", m_var);
			m_var = {WIDTH{1'b1}};   // Workaround - Use concatenation operator to club together as many 1s required
			$display("m_var=0x%0h", m_var);
		end

		/*
			m_var=0x0
			m_var=0xzz
			m_var=0xxx
			m_var=0x1
			m_var=0xff
		*/

		begin
			m_var1 = '1;
			m_var2 = '1;
			$display("m_var1=0x%0h  m_var2=0x%0h", m_var1, m_var2);

			// This does not work - Radix must be specified !
			//m_var1 = 'F0;
			//m_var2 = 'cafe;
		end

		/*
			m_var1=0xff  m_var2=0xffff
		*/

		begin
			pi   = 3.14;    // Store floating point number
			freq = 1e6; 	// Store exponential number
			$display ("Value of pi = %f", pi);
			$display ("Value of pi = %0.3f", pi);
			$display ("Value of freq = %0d", freq);
		end

		/*
			Value of pi = 3.140000
			Value of pi = 3.140
			Value of freq = 1000000
		*/

		begin
			x_val = 4'b01zx;

			// If a logic type or any 4-state variable assigns its value to a "bit" type
			// variable, then X and Z get converted to zero
			var_b = x_val;
			$display ("x_val=%b var_b = %b", x_val, var_b);
		end

		/*
			x_val=01zx var_b = 0100
		*/

		begin
			// Initial value of "bit" data type is 0
			$display ("Initial value var_a1=%0b var_b1=0x%0h", var_a1, var_b1);

			// Assign new values and display the variable to see that it gets the new values
			var_a1 = 1;
			var_b1 = 4'hF;
			$display ("New values    var_a1=%0b var_b1=0x%0h", var_a1, var_b1);

			// If a "bit" type variable is assigned with a value greater than it can hold
			// the left most bits are truncated. In this case, var_b1 can hold only 4 bits
			// and hence 'h481 gets truncated leaving var_b with only 'ha;
			var_b1 = 16'h481a;
			$display ("Truncated value: var_b1=0x%0h", var_b1);
		end
		
		/*
			Initial value var_a1=0 var_b1=0x0
			New values    var_a1=1 var_b1=0xf
			Truncated value: var_b1=0xa
		*/
	end

	initial begin

		#10 m_var_s  = 0;           // assign 0
		#20 m_var_s  = 2**7 - 1; 	// assign 127
		#30 m_var_s  = 2**7;        // assign 128
		#40 m_var_s  = 2**8 - 1;    // assign 255
	end

	initial
		$monitor("[%0t] m_var_s = 'd%0d  (0x%0h)", $time, m_var_s, m_var_s);

	/*
		[0] m_var_s = 'd0  (0x0)
		[30] m_var_s = 'd127  (0x7f)
		[60] m_var_s = 'd-128  (0x80)
		[100] m_var_s = 'd-1  (0xff)
	*/

endmodule