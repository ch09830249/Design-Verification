// Dynamic Array of Associative Array
module tb;
  // Create an associative array with key of type string and value of type int
  // for each index in a dynamic array
  int fruits [] [string];

  initial begin
    // Create a dynamic array with size 2 (Runtime 才指定 size 為 2)
    fruits = new [2];

    // Initialize the associative array inside each dynamic array index
    fruits [0] = '{ "apple" : 1, "grape" : 2 };
    fruits [1] = '{ "melon" : 3, "cherry" : 4 };

    // Iterate through each index of dynamic array
    foreach (fruits[i])
      // Iterate through each key of the current index in dynamic array
      foreach (fruits[i][fruit])
        $display ("fruits[%0d][%s] = %0d", i, fruit, fruits[i][fruit]);

  end
endmodule

/*
    fruits[0][apple] = 1
    fruits[0][grape] = 2
    fruits[1][cherry] = 4
    fruits[1][melon] = 3
*/