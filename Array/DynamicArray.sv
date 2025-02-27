/*
  A dynamic array is an unpacked array whose size can be set or changed at run time
  The default size of a dynamic array is zero until it is set by the new() constructor.
  A dynamic array dimensions are specified by the empty square brackets [ ].
  The new() function is used to allocate a size for the array and initialize its elements if required.

  [data_type] [identifier_name]  [];

    EX:
      bit [7:0] 	stack []; 		// A dynamic array of 8-bit vector
      string 		names []; 		// A dynamic array that can contain strings
*/

module tb;
	// Create a dynamic array that can hold elements of type int
	int array [];

	initial begin
		// Create a size for the dynamic array -> size here is 5
		// so that it can hold 5 values
		array = new [5];

		// Initialize the array with five values
		array = '{31, 67, 10, 4, 99};

		// Loop through the array and print their values
		foreach (array[i])
			$display ("array[%0d] = %0d", i, array[i]);
	end
endmodule

/*
  array[0] = 31
  array[1] = 67
  array[2] = 10
  array[3] = 4
  array[4] = 99
*/