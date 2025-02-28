/*
  Method	    Description
  sum()	    Returns the sum of all array elements
  product()	Returns the product of all array elements
  and()	    Returns the bitwise AND (&) of all array elements
  or()	    Returns the bitwise OR (|) of all array elements
  xor()	    Returns the bitwise XOR (^) of all array elements
*/

module tb;
  int array[4] = '{1, 2, 3, 4};

  initial begin
    $display ("sum     = %0d", array.sum());
    $display ("product = %0d", array.product());
    $display ("and     = 0x%0h", array.and());
    $display ("or      = 0x%0h", array.or());
    $display ("xor     = 0x%0h", array.xor());
  end
endmodule

/*
  sum     = 10
  product = 24
  and     = 0x0
  or      = 0x7
  xor     = 0x4
*/