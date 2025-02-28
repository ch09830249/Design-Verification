module tb;
	// Create a queue that can store "string" values
	string   fruits[$] =  { "orange", "apple", "lemon", "kiwi" };

	initial begin
		// Select a subset of the queue
		$display ("citrus fruits = %p", fruits[1:2]);

		// Get elements from index 1 to end of queue
		$display ("fruits = %p", fruits[1:$]);

		// Add element to the end of queue
		fruits[$+1] = "pineapple";
		$display ("fruits = %p", fruits);

		// Delete first element
		$display ("Remove orange, fruits = %p", fruits[1:$]);
	end
endmodule

/*
	citrus fruits = '{"apple", "lemon"} 
	fruits = '{"apple", "lemon", "kiwi"} 
	fruits = '{"orange", "apple", "lemon", "kiwi", "pineapple"} 
	Remove orange, fruits = '{"apple", "lemon", "kiwi", "pineapple"} 
*/