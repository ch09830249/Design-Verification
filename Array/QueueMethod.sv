/* 和 C++ 很像
	Methods																	Description
function int size ();												Returns the number of items in the queue, 0 if empty
function void insert (input integer index, input element_t item);	Inserts the given item at the specified index position
function void delete ( [input integer index] );						Deletes the element at the specified index, and if not provided all elements will be deleted
function element_t pop_front ();									Removes and returns the first element of the queue
function element_t pop_back ();										Removes and returns the last element of the queue
function void push_front (input element_t item);					Inserts the given element at the front of the queue
function void push_back (input element_t item);						Inserts the given element at the end of the queue
*/

module tb;
	string fruits[$] = {"apple", "pear", "mango", "banana"};

	initial begin
		// size() - Gets size of the given queue
		$display ("Number of fruits=%0d", fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// insert() - Insert an element to the given index
		fruits.insert (1, "peach");
		$display ("Insert peach, size=%0d", fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// delete() - Delete element at given index
		fruits.delete (3);
		$display ("Delete mango, size=%0d", fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// pop_front() - Pop out element at the front
		$display ("Pop %s,    size=%0d", fruits.pop_front(), fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// push_front() - Push a new element to front of the queue
		fruits.push_front("apricot");
		$display ("Push apricot, size=%0d", fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// pop_back() - Pop out element from the back
		$display ("Pop %s,   size=%0d", fruits.pop_back(), fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");

		// push_back() - Push element to the back
		fruits.push_back("plum");
		$display ("Push plum,    size=%0d", fruits.size());
		foreach (fruits[i])
    		$display ("fruits[%0d] = %s", i, fruits[i]);
		$display ("===================");
	end
endmodule

/*
	Number of fruits=4
	fruits[0] = apple
	fruits[1] = pear
	fruits[2] = mango
	fruits[3] = banana
	===================
	Insert peach, size=5
	fruits[0] = apple
	fruits[1] = peach
	fruits[2] = pear
	fruits[3] = mango
	fruits[4] = banana
	===================
	Delete mango, size=4
	fruits[0] = apple
	fruits[1] = peach
	fruits[2] = pear
	fruits[3] = banana
	===================
	Pop apple,    size=3
	fruits[0] = peach
	fruits[1] = pear
	fruits[2] = banana
	===================
	Push apricot, size=4
	fruits[0] = apricot
	fruits[1] = peach
	fruits[2] = pear
	fruits[3] = banana
	===================
	Pop banana,   size=3
	fruits[0] = apricot
	fruits[1] = peach
	fruits[2] = pear
	===================
	Push plum,    size=4
	fruits[0] = apricot
	fruits[1] = peach
	fruits[2] = pear
	fruits[3] = plum
	===================
*/