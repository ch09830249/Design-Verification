/*
  Optional With: 若是有 with, 就是計算後面 expression, 再去比較值

  Methods	          Description
  min()	          Returns the element with minimum value or whose expression evaluates to a minimum   若是有 with, 就是計算後面 expression 結果最小的值放到 result
  max()	          Returns the element with maximum value or whose expression evaluates to a maximum
  unique()	      Returns all elements with unique values or whose expression evaluates to a unique value
  unique_index()	Returns the indices of all elements with unique values or whose expression evaluates to a unique value
*/

module tb;
  int array[9] = '{4, 7, 2, 5, 7, 1, 6, 3, 1};
  int res[$];

  initial begin
    res = array.min();
    $display ("min          : %p", res);

    res = array.max();
    $display ("max          : %p", res);

    res = array.unique();
    $display ("unique       : %p", res);

    res = array.unique(x) with (x < 3);
    $display ("unique       : %p", res);

    res = array.unique_index;
    $display ("unique_index : %p", res);
  end
endmodule

/*
  min          : '{1}
  max          : '{7}
  unique       : '{4, 7, 2, 5, 1, 6, 3}
  unique       : '{4, 2}                  4: True, 2: false
  unique_index : '{0, 1, 2, 3, 5, 6, 7}   回傳出現該值的第一個 index
*/