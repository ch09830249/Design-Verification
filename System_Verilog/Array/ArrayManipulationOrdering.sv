/*
  Method	      Description
reverse()	  Reverses the order of elements in the array
sort()	    Sorts the array in ascending order, optionally using with clause        with 用於 class, 後面會有例子
rsort()	    Sorts the array in descending order, optionally using with clause
shuffle()	  Randomizes the order of the elements in the array. with clause is not allowed here.
*/

module tb;
  int array[9] = '{4, 7, 2, 5, 7, 1, 6, 3, 1};

  initial begin
    array.reverse();
    $display ("reverse  : %p", array);

    array.sort();
    $display ("sort     : %p", array);

    array.rsort();
    $display ("rsort    : %p", array);

    for (int i = 0; i < 5; i++) begin
    	array.shuffle();
      $display ("shuffle Iter:%0d  = %p", i, array);
    end
  end
endmodule

/*
  reverse  : '{1, 3, 6, 1, 7, 5, 2, 7, 4}
  sort     : '{1, 1, 2, 3, 4, 5, 6, 7, 7}
  rsort    : '{7, 7, 6, 5, 4, 3, 2, 1, 1}
  shuffle Iter:0  = '{6, 7, 1, 7, 3, 2, 1, 4, 5}
  shuffle Iter:1  = '{5, 1, 3, 4, 2, 7, 1, 7, 6}
  shuffle Iter:2  = '{3, 1, 7, 4, 6, 7, 1, 2, 5}
  shuffle Iter:3  = '{6, 4, 7, 3, 1, 7, 5, 2, 1}
  shuffle Iter:4  = '{3, 6, 2, 5, 4, 7, 7, 1, 1}
*/