/*
	Syntax:
		// Value     Array_Name          [ key ];
		data_type    array_identifier    [ index_type ];

	1. Associative arrays do not have any storage allocated until it is used.
	2. The index expression is not restricted to integral expressions. (Like dictionary in Python)
	3. Ordering	(Based on the index type)

	Method:
			Function													Description
		function int num ();						Returns the number of entries in the associative array											num 和 size 好像一樣, 都是 entries 數量
		function int size ();						Also returns the number of entries, if empty 0 is returned
		function void delete ( [input index] );		index when specified deletes the entry at that index, else the whole array is deleted
		function int exists (input index);			Checks whether an element exists at specified index; returns 1 if it does, else 0
		function int first (ref index);				Assigns to the given index variable the value of the first index; returns 0 for empty array		回傳第一個元素的 index
		function int last (ref index);				Assigns to given index variable the value of the last index; returns 0 for empty array			回傳最後一個元素的 index
		function int next (ref index);				Finds the smallest index whose value is greater than the given index							指定 index, 回傳下一個 entry 的 index
		function int prev (ref index);				Finds the largest index whose value is smaller than the given index								指定 index, 回傳上一個 entry 的 index
*/

// Initialization
module tb;

	int   	array1 [int]; 			// An integer array with integer index
	int   	array2 [string]; 		// An integer array with string index
	string  array3 [string]; 		// A string array with string index

  	initial begin
      	// Initialize each dynamic array with some values
    	array1 = '{ 1 : 22,
	            	6 : 34 };

		array2 = '{ "Ross" : 100,
	            	"Joey" : 60 };

		array3 = '{ "Apples" : "Oranges",
	            	"Pears" : "44" };

      	// Print each array
		$display ("array1 = %p", array1);
		$display ("array2 = %p", array2);
		$display ("array3 = %p", array3);
    end
endmodule
