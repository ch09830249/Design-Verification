// All methods
module tb;
    int      fruits_l0 [string];

    initial begin
      fruits_l0 = '{ "apple"  : 4,
                     "orange" : 10,
                     "plum"   : 9,
                     "guava"  : 1 };
	/*
	Ordering
		fruits_l0 = '{ "apple"  : 4,
					   "guava"  : 1.
					   "orange" : 10,
					   "plum"   : 9};
	*/


      // size() : Print the number of items in the given dynamic array
      $display ("fruits_l0.size() = %0d", fruits_l0.size());	// fruits_l0.size() = 4


      // num() : Another function to print number of items in given array
      $display ("fruits_l0.num() = %0d", fruits_l0.num());		// fruits_l0.num() = 4


      // exists() : Check if a particular key exists in this dynamic array
      if (fruits_l0.exists ("orange"))
        $display ("Found %0d orange !", fruits_l0["orange"]);	// Found 10 orange !

      if (!fruits_l0.exists ("apricots"))
        $display ("Sorry, season for apricots is over ...");	// Sorry, season for apricots is over ...

      // Note: String indices are taken in alphabetical order
      // first() : Get the first element in the array
      begin
      	string f;
        // This function returns true if it succeeded and first key is stored
        // in the provided string "f"
        if (fruits_l0.first (f))
          $display ("fruits_l0.first [%s] = %0d", f, fruits_l0[f]);		// fruits_l0.first [apple] = 4
      end

      // last() : Get the last element in the array
      begin
        string f;
        if (fruits_l0.last (f))
          $display ("fruits_l0.last [%s] = %0d", f, fruits_l0[f]);		// fruits_l0.last [plum] = 9
      end

      // prev() : Get the previous element in the array
      begin
        string f = "orange";
        if (fruits_l0.prev (f))
          $display ("fruits_l0.prev [%s] = %0d", f, fruits_l0[f]);		// fruits_l0.prev [guava] = 1
      end

      // next() : Get the next item in the array
      begin
        string f = "orange";
        if (fruits_l0.next (f))
          $display ("fruits_l0.next [%s] = %0d", f, fruits_l0[f]);		// fruits_l0.next [plum] = 9
      end
    end
endmodule
