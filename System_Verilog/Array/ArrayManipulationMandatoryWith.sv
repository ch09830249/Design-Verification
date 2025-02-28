/*
  These methods are used to filter out certain elements from an existing array based on a given expression.
  All such elements that satisfy the given expression is put into an array and returned. 
  Hence the with clause is mandatory for the following methods.

  Method name	            Description
  find()	            Returns all elements satisfying the given expression
  find_index()	      Returns the indices of all elements satisfying the given expression
  find_first()	      Returns the first element satisfying the given expression
  find_first_index()	Returns the index of the first element satisfying the given expression
  find_last()	        Returns the last element satisfying the given expression
  find_last_index()	  Returns the index of the last element satisfying the given expression
*/

module tb;
  int array[9] = '{4, 7, 2, 5, 7, 1, 6, 3, 1};
  int res[$];

  initial begin
    res = array.find(x) with (x > 3);
    $display ("find(x)         : %p", res);

    res = array.find_index with (item == 4);
    $display ("find_index      : res[%0d] = 4", res[0]);

    res = array.find_first with (item < 5 & item >= 3);
    $display ("find_first      : %p", res);

    res = array.find_first_index(x) with (x > 5);
    $display ("find_first_index: %p", res);

    res = array.find_last with (item <= 7 & item > 3);
    $display ("find_last       : %p", res);

    res = array.find_last_index(x) with (x < 3);
    $display ("find_last_index : %p", res);
  end
endmodule

/*
  find(x)         : '{4, 7, 5, 7, 6}
  find_index      : res[0] = 4
  find_first      : '{4}
  find_first_index: '{1}
  find_last       : '{6}
  find_last_index : '{8}
*/