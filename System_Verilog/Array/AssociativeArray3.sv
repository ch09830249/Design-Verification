// Create a new typedef that represents a dynamic array
typedef int int_da [];

module tb;
  // Create an associative array where key is a string
  // and value is a dynamic array
  int_da fruits [string];

  initial begin
    // For key "apple", create a dynamic array that can hold 2 items
    fruits ["apple"] = new [2];

    // Initialize the dynamic array with some values
    fruits ["apple"] = '{ 4, 5};

    // Iterate through each key, where key represented by str1
    foreach (fruits[str1])
      // Iterate through each item inside the current dynamic array ie.fruits[str1]
      foreach (fruits[str1][i])
        $display ("fruits[%s][%0d] = %0d", str1, i, fruits[str1][i]);

  end
endmodule

/*
  fruits[apple][0] = 4
  fruits[apple][1] = 5
*/