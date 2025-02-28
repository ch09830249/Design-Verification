// Declare a dynamic array to store strings as a datatype
typedef string str_da [];

module tb;
  // This is a queue of dynamic arrays
  str_da list [$];

  initial begin
    // Initialize separate dynamic arrays with some values
    str_da marvel = '{"Spiderman", "Hulk", "Captain America", "Iron Man"};
    str_da dcWorld = '{"Batman", "Superman" };

    // Push the previously created dynamic arrays to queue
    list.push_back (marvel);
    list.push_back (dcWorld);

    // Iterate through the queue and access dynamic array elements
    foreach (list[i])
      foreach (list[i][j])
        $display ("list[%0d][%0d] = %s", i, j, list[i][j]);

    // Simply print the queue
    $display ("list = %p", list);
  end
endmodule

/*
  list[0][0] = Spiderman
  list[0][1] = Hulk
  list[0][2] = Captain America
  list[0][3] = Iron Man
  list[1][0] = Batman
  list[1][1] = Superman
  list = '{'{"Spiderman", "Hulk", "Captain America", "Iron Man"}, '{"Batman", "Superman"}}
*/