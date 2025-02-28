// Define a class with a single string member called "name"
class Fruit;
  string name;

  function new (string name="Unknown");
   	this.name = name;
  endfunction
endclass

module tb;
  // Create a queue that can hold values of data type "Fruit"
  Fruit list [$];

  initial begin
    // Create a new class object and call it "Apple"
    // and push into the queue
    Fruit f = new ("Apple");
    list.push_back (f);

    // Create another class object and call it "Banana" and
    // push into the queue
    f = new ("Banana");
    list.push_back (f);

    // Iterate through queue and access each class object
    foreach (list[i])
      $display ("list[%0d] = %s", i, list[i].name);

    // Simply print the whole queue, note that class handles are printed
    // and not class object contents
    $display ("list = %p", list);
  end
endmodule

/*
	list[0] = Apple
	list[1] = Banana
	list = '{$unit_0x4ccdf83b::Fruit@2_1, $unit_0x4ccdf83b::Fruit@4_1}
*/