/*
    Add new item into dynamic array

		int array [];
		array = new [10];

		// This creates one more slot in the array, while keeping old contents
		array = new [array.size() + 1] (array);
*/

module tb;
	// Create two dynamic arrays of type int	創建兩個 handle
	int array [];
	int id [];

	initial begin
		// Allocate 5 memory locations to "array" and initialize with values
		array = new [5];
		array = '{1, 2, 3, 4, 5};

		// Point "id" to "array"
		id = array;

		// Display contents of "id"
		$display ("=== id ===");
		foreach (id[i])
			$display ("id[%0d] = %0d", i, array[i]);

		// Grow size by 1 and copy existing elements to the new dyn.Array "id"
		id = new [id.size() + 1] (id);

		// Assign value 6 to the newly added location [index 5]
		id [id.size() - 1] = 6;

		// Display contents of new "id"
		$display ("=== New id ===");
		foreach (id[i])
			$display ("id[%0d] = %0d", i, id[i]);

		// Display size of both arrays
		$display ("array.size() = %0d, id.size() = %0d", array.size(), id.size());
	end
endmodule

/*
	=== id ===
	id[0] = 1
	id[1] = 2
	id[2] = 3
	id[3] = 4
	id[4] = 5
	=== New id ===
	id[0] = 1
	id[1] = 2
	id[2] = 3
	id[3] = 4
	id[4] = 5
	id[5] = 6
	array.size() = 5, id.size() = 6
*/

/*
id = '{1, 2, 3, 4, 5}
New id = '{1, 2, 3, 4, 5, 6}
array.size() = 5, id.size() = 6
*/